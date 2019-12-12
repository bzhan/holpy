# Author: Bohua Zhan

from copy import copy, deepcopy
import os
import inspect
import json

from kernel import term
from kernel.term import Var
from kernel.theory import Theory, TheoryException
from kernel.thm import Thm
from kernel import extension
from logic.context import Context
from logic import induct
from logic import logic  # Load all defined macros
from data import expr
from syntax import parser
from syntax import operator
from prover import z3wrapper
from server import items
from server import method  # Load all defined methods


"""
Cache of parsed theories.

The dictionary is indexed by user, and then by theory name.

Each theory stores a 'timestamp' field, for the last modification
time of the corresponding file.

In the contents, instead of each item is the parsed item as
well as the corresponding extension.

"""
theory_cache = dict()

"""
Cache of item mapping.

The dictionary is indexed by user. For each user, it is a
mapping from (ty, name) to (theory_name, timestamp, index).

"""
item_index = dict()


def user_dir(username="master"):
    """Returns directory for the user."""
    assert username, "user_dir: empty username."
    if username == 'master':
        return './library/'
    else:
        return './users/' + username

def user_file(filename, username="master"):
    """Return json file for the user and given filename."""
    assert username, "user_file: empty username."
    if username == 'master':
        return './library/' + filename + '.json'
    else:
        return './users/' + username + '/' + filename + '.json'

def load_json_data(filename, username="master"):
    """Load json data for the given theory name and user."""
    with open(user_file(filename, username), encoding='utf-8') as f:
        return json.load(f)

def load_metadata(username="master"):
    """For the given user, load metadata for all theory files."""
    theory_cache[username] = dict()
    item_index[username] = dict()
    for f in os.listdir(user_dir(username)):
        if f.endswith('.json'):
            filename = f[:-5]
            data = load_json_data(filename, username)
            timestamp = os.path.getmtime(user_file(filename, username))
            theory_cache[username][filename] = {
                'imports': data['imports'],
                'description': data['description']
            }

    # Immediately check for topological order.
    check_topological_sort()

def check_topological_sort(username="master"):
    """For the given user, check the import relations have no cycles."""
    for name in theory_cache[username].keys():
        theory_cache[username][name]['visited'] = False
    
    count = 0
    def dfs(name, path):
        """Perform depth-first search.

        name - current theory name.
        path - list of theory names on the current search path,
               not including the current theory.

        """
        nonlocal count
        if theory_cache[username][name]['visited']:
            return

        if name in path:
            id = path.index(name)
            cycle = path[id:] + (name,)
            raise TheoryException("Cycle in imports: %s" % (', '.join(cycle)))

        for import_name in theory_cache[username][name]['imports']:
            dfs(import_name, path + (name,))
        theory_cache[username][name]['order'] = count
        theory_cache[username][name]['visited'] = True
        count += 1

    for name in sorted(theory_cache[username].keys()):
        if not theory_cache[username][name]['visited']:
            dfs(name, tuple())

def get_import_order(filenames, username="master"):
    """Obtain the order of loading theories for fulfilling
    the imports in the theory given by the list of filenames.

    """
    if username not in theory_cache:
        load_metadata(username)

    depend_list = []
    def dfs(name):
        if name in depend_list:
            return
        else:
            for import_name in theory_cache[username][name]['imports']:
                dfs(import_name)
            depend_list.append(name)
    
    for name in filenames:
        dfs(name)

    return depend_list

def load_theory_cache(filename, username="master"):
    """Load the content of the given theory into cache.
    
    Return the theory cache as a dictionary.

    """
    if username not in theory_cache:
        load_metadata(username)

    cache = theory_cache[username][filename]
    timestamp = os.path.getmtime(user_file(filename, username))

    if 'timestamp' in cache and timestamp == cache['timestamp']:
        # No need to update cache
        return cache

    # Load all imported theories
    depend_list = get_import_order(cache['imports'], username)
    thy = Theory.EmptyTheory()
    for prev_name in depend_list:
        prev_cache = load_theory_cache(prev_name, username)
        for item in prev_cache['content']:
            if item.error is None:
                thy.unchecked_extend(item.get_extension())

    # Use this theory to parse the content of current theory
    cache['timestamp'] = timestamp
    data = load_json_data(filename, username)
    cache['content'] = []
    for index, item in enumerate(data['content']):
        item = items.parse_item(thy, item)
        cache['content'].append(item)
        if item.error is None:
            exts = item.get_extension()
            thy.unchecked_extend(exts)
            for ext in exts:
                if ext.ty == extension.CONSTANT:
                    name = ext.ref_name
                else:
                    name = ext.name
                item_index[username][(ext.ty, name)] = (filename, timestamp, index)

    return cache

def query_item_index(username, filename, ext_ty, name):
    """Query the item index."""

    # Make sure the theory (and all its dependencies) are indexed
    load_theory_cache(filename, username)

    if (ext_ty, name) in item_index[username]:
        filename, timestamp, index = item_index[username][(ext_ty, name)]
        if timestamp == os.path.getmtime(user_file(filename, username)):
            return filename, index
        else:
            return None
    else:
        return None

def load_theories(filenames, username="master"):
    """Load a list of theories (usually serve as a base for
    extending a theory).
    
    """
    depend_list = get_import_order(filenames, username)
    thy = Theory.EmptyTheory()
    for prev_name in depend_list:
        prev_cache = load_theory_cache(prev_name, username)
        for item in prev_cache['content']:
            if item.error is None:
                thy.unchecked_extend(item.get_extension())

    return thy


def load_theory(filename, *, limit=None, username="master"):
    """Load the theory with the given theory name.
    
    Optional limit is a pair (ty, name) specifying the first item
    that should not be loaded.
    
    """
    load_theory_cache(filename, username)
    
    cache = theory_cache[username][filename]
    thy = load_theories(cache['imports'], username)
        
    # Take the portion of content up to (and not including) limit
    content = cache['content']
    found_limit = False
    for item in content:
        if limit and item.ty == limit[0] and item.name == limit[1]:
            found_limit = True
            break

        if item.error is None:
            thy.unchecked_extend(item.get_extension())

    if limit and not found_limit:
        raise TheoryException("load_theory: limit %s not found" % str(limit))

    return thy
