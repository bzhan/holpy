# Author: Bohua Zhan

from kernel.type import TFun, Type
from kernel.term import Term, Const
from data.binary import to_binary, is_binary, from_binary
from data.nat import natT
from data.list import listT, mk_literal_list, is_literal_list, dest_literal_list

"""Utility functions for characters and strings."""

charT = Type("char")
stringT = Type("string")

Char = Const("Char", TFun(natT, charT))
String = Const("String", TFun(listT(charT), stringT))

def mk_char(c):
    """Given a Python string of length 1, return the corresponding
    HOL character.

    """
    assert isinstance(c, str) and len(c) == 1, "mk_char: expect a string of length 1"
    return Char(to_binary(ord(c)))

def mk_string(s):
    """Given a Python string, return the corresponding HOL string."""
    assert isinstance(s, str), "mk_string: expect a string"
    return String(mk_literal_list([mk_char(c) for c in s], charT))

def is_char(t):
    """Whether the given term is a HOL character."""
    assert isinstance(t, Term), "is_char"
    return t.is_comb() and t.fun == Char and is_binary(t.arg)

def is_string(t):
    """Whether the given term is a HOL string."""
    assert isinstance(t, Term), "is_string"
    return t.is_comb() and t.fun == String and is_literal_list(t.arg) and \
        all(is_char(c) for c in dest_literal_list(t.arg))

def dest_char(t):
    """Given a HOL character, return the corresponding Python string
    of length 1.

    """
    assert isinstance(t, Term), "dest_char"
    assert t.is_comb() and t.fun == Char and is_binary(t.arg), "dest_char"
    return chr(from_binary(t.arg))

def dest_string(t):
    """Given a HOL string, return the corresponding Python string."""
    assert isinstance(t, Term), "dest_string"
    assert t.is_comb() and t.fun == String and is_literal_list(t.arg), "dest_string"
    return ''.join(dest_char(c) for c in dest_literal_list(t.arg))
