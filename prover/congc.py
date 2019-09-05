"""Implementation of congruence closure algorithm.

Reference: Fast congruence closure and extensions
by Robert Nieuwenhuis and Albert Oliveras.

"""

from queue import Queue

from kernel import term
from syntax import printer

PENDING_CONST, PENDING_COMB = range(2)

class CongClosure:
    """Data structure for congruence closure."""

    def __init__(self):
        """Initialization with the empty data structure.
        
        Each equation is either in the form
        (a, b) for a = b or
        ((a1, a2), a) for f(a1, a2) = a.

        """
        # List of equations to be processed. Should be empty
        # after each run of merge.
        # Each element of pending is either
        # (PENDING_CONST, a, b) or
        # (PENDING_COMB, ((a1, a2), a), ((b1, b2), b))
        self.pending = Queue()

        # Dictionary from constants to its current representative.
        self.rep = {}

        # Dictionary from representatives to the list of all constants
        # in its class.
        self.class_list = {}

        # Dictionary from representatives to the list of input
        # equations they appear in.
        self.use_list = {}

        # Dictionary from pairs of representatives to some
        # input equation in which they appear in.
        self.lookup = {}

        # Proof forest: represents a graph where each node points to
        # its parent in the forest. If the node is a root, then
        # proof_forest[node] is None. Otherwise it is the pair (p, label),
        # where label is an element of PENDING that created the edge.
        self.proof_forest = {}

    def __str__(self):
        def print_eq(eq):
            s, t = eq
            if isinstance(s, str):
                return "%s = %s" % (s, t)
            else:
                a1, a2 = s
                return "f(%s, %s) = %s" % (a1, a2, t)

        def print_pending(pending):
            if pending[0] == PENDING_CONST:
                _, a, b = pending
                return "%s = %s" % (a, b)
            else:
                _, ((a1, a2), a), ((b1, b2), b) = pending
                return "(f(%s, %s) = %s, f(%s, %s) = %s)" % (a1, a2, a, b1, b2, b)

        pending = "\n".join(print_pending(p) for p in self.pending.queue)
        rep = "{%s}" % (", ".join("%s: %s" % (s, t) for s, t in self.rep.items()))
        class_list = "\n".join("%s: %s" % (s, ", ".join(t))
                               for s, t in self.class_list.items())
        use_list = "\n".join("%s: %s" % (s, ", ".join(print_eq(eq) for eq in t))
                             for s, t in self.use_list.items() if len(t) > 0)
        lookup = "\n".join("%s, %s: %s" % (p[0], p[1], print_eq(eq))
                           for p, eq in self.lookup.items())
        proof_forest = "\n".join("%s: %s, %s" % (s, p[0], print_pending(p[1]))
                                 for s, p in self.proof_forest.items() if p is not None)

        return "Pending:\n" + pending + "\nrep:\n" + rep + "\nclass_list:\n" + class_list + \
            "\nuse_list\n" + use_list + "\nlookup\n" + lookup + "\nforest\n" + proof_forest

    def add_var(self, s):
        """Add new variable."""
        assert isinstance(s, str)
        if s not in self.rep:
            self.rep[s] = s
            self.class_list[s] = [s]
            self.use_list[s] = []
            self.proof_forest[s] = None

    def merge(self, s, t):
        """Merge terms s and t. s must be either a string or a pair
        of strings (for f(s1, s2)). t must be a string.

        """
        assert isinstance(t, str)
        self.add_var(t)
        if isinstance(s, str):
            self.add_var(s)
            self.pending.put((PENDING_CONST, s, t))
            self._propagate()
        else:
            a1, a2 = s
            assert isinstance(a1, str) and isinstance(a2, str)
            self.add_var(a1)
            self.add_var(a2)
            rep_a1, rep_a2 = self.rep[a1], self.rep[a2]
            if (rep_a1, rep_a2) in self.lookup:
                eq2 = self.lookup[(rep_a1, rep_a2)]
                self.pending.put((PENDING_COMB, (s, t), eq2))
                self._propagate()
            else:
                self.lookup[(rep_a1, rep_a2)] = (s, t)
                self.use_list[rep_a1].append((s, t))
                self.use_list[rep_a2].append((s, t))

    def _path_to_root(self, s):
        """Find the path to root of s."""
        path_to_root = [(s, None)]
        while self.proof_forest[s] is not None:
            ps, l = self.proof_forest[s]
            path_to_root.append((ps, l))
            s = ps
        return path_to_root

    def _add_edge_proof_forest(self, s1, s2, label):
        """Add edge s1 to s2 to the proof forest. Note s1 and s2 does not
        need to be roots.

        Assume the tree for s2 is at least as large as that for s1. First
        find the path to the root of s1. Then redirect s1 to s2, and
        reverse all edges on the path.
        
        """
        path_to_root = self._path_to_root(s1)
        self.proof_forest[s1] = (s2, label)
        for i in range(len(path_to_root) - 1):
            ps, label = path_to_root[i+1]
            s, _ = path_to_root[i]
            self.proof_forest[ps] = (s, label)

    def _propagate(self):
        """Propagation. Removes one equation from pending."""
        while not self.pending.empty():
            E = self.pending.get()

            # Extract the two elements being assigned equal
            if E[0] == PENDING_CONST:
                _, a, b = E
            else:
                _, (_, a), (_, b) = E

            rep_a, rep_b = self.rep[a], self.rep[b]
            if rep_a != rep_b:
                # Ensure the class_list for a is smaller or equal to
                # class_list for b.
                if len(self.class_list[rep_a]) > len(self.class_list[rep_b]):
                    a, b = b, a
                    rep_a, rep_b = rep_b, rep_a

                # Update the proof forest.
                self._add_edge_proof_forest(a, b, E)

                # Move class_list of a to b.
                for c in self.class_list[rep_a]:
                    self.rep[c] = rep_b
                self.class_list[rep_b] += self.class_list[rep_a]
                del self.class_list[rep_a]

                # Process use_list of rep_a, move to rep_b if does not
                # trigger new equation. 
                for eq in self.use_list[rep_a]:
                    (c1, c2), c = eq
                    rep_c1, rep_c2 = self.rep[c1], self.rep[c2]
                    if (rep_c1, rep_c2) in self.lookup:
                        eq2 = self.lookup[(rep_c1, rep_c2)]
                        self.pending.put((PENDING_COMB, eq, eq2))
                    else:
                        self.lookup[(rep_c1, rep_c2)] = eq
                        self.use_list[rep_b].append(eq)
                del self.use_list[rep_a]

    def explain(self, s, t, *, res=None):
        """Explain the equality between two constants.
        
        This makes use of proof_forest. It first finds the common
        ancestor of s and t in the forest, then add to the path from
        s to t through the common ancestor into the explanation.

        If on the path there are equations of form PENDING_COMB,
        recursive calls to explain are made to explain equality
        of the arguments.

        """
        # res is the dictionary from pairs of points to a path between them.
        if res is None:
            res = dict()

        # If s == t or res already contains the path, do nothing.
        if s == t or (s, t) in res:
            return res

        s_path = self._path_to_root(s)
        t_path = self._path_to_root(t)

        assert s_path[-1][0] == t_path[-1][0], "explain: s and t are not in the same tree"

        # Traverse back. pos is the number of nodes from the root.
        pos = 1
        len_s = len(s_path)
        len_t = len(t_path)
        while len_s >= pos + 1 and len_t >= pos + 1 and \
              s_path[len_s-pos-1][0] == t_path[len_t-pos-1][0]:
            pos += 1

        # Now len_s-pos and len_t-pos are the same, and is the lowest
        # common ancestor.
        cur_path = []
        for i in range(1, len_s-pos+1):
            _, eq = s_path[i]
            cur_path.append(eq)
        for i in reversed(range(len_t-pos)):
            _, eq = t_path[i+1]
            cur_path.append(eq)

        # Make recursive calls to explain for PENDING_COMB edges
        for eq in cur_path:
            if eq[0] == PENDING_COMB:
                _, ((a1, a2), a), ((b1, b2), b) = eq
                self.explain(a1, b1, res=res)
                self.explain(a2, b2, res=res)

        res[(s, t)] = cur_path
        return res

    def test(self, t1, t2):
        """Test whether t1 is equal to t2."""
        assert isinstance(t1, str) and isinstance(t2, str)
        return self.rep[t1] == self.rep[t2]


class CongClosureHOL:
    """Wrapper around congruence closure, for handling terms in
    higher-order logic.

    """
    def __init__(self, thy):
        """Initialization of an empty congruence closure for terms in
        higher-order logic.

        """
        # Number of constants used.
        self.num_consts = 0

        # Mapping from constants (strings) to atomic terms.
        self.index = {}

        # Inverse mapping from atomic terms to constants.
        self.rev_index = {}

        # Core data structure
        self.closure = CongClosure()

        # Keep a theory for printing purposes
        self.thy = thy

    def __str__(self):
        index = "\n".join("%s: %s" % (s, printer.print_term(self.thy, t))
                          for s, t in self.index.items())
        return "Index:\n" + index + "\nClosure:\n" + str(self.closure)

    def add_const(self, t):
        """Add a new constant representing t."""
        assert t not in self.rev_index, "add_atomic_term: t already exists."
        self.num_consts += 1
        new_var = "s" + str(self.num_consts)
        self.index[new_var] = t
        self.rev_index[t] = new_var
        self.closure.add_var(new_var)
        return new_var

    def add_term(self, t):
        """Add the term to the congruence closure. If successful (the
        term is not an open term), return the string representing the term.
        Otherwise (if the term is open), return None.
        
        """
        if t in self.rev_index:
            return self.rev_index[t]

        if t.ty == term.Term.VAR or t.ty == term.Term.CONST:
            return self.add_const(t)
        elif t.ty == term.Term.COMB:
            fun_var = self.add_term(t.fun)
            arg_var = self.add_term(t.arg)
            if fun_var and arg_var:
                t_var = self.add_const(t)
                self.closure.merge((fun_var, arg_var), t_var)
                return t_var
            else:
                return None
        elif t.ty == term.Term.ABS:
            self.add_term(t.body)
            return self.add_const(t)
        elif t.ty == term.Term.BOUND:
            return None
        else:
            raise TypeError

    def merge(self, s, t):
        u1 = self.add_term(s)
        u2 = self.add_term(t)
        self.closure.merge(u1, u2)

    def test(self, t1, t2):
        u1 = self.add_term(t1)
        u2 = self.add_term(t2)
        return self.closure.test(u1, u2)
