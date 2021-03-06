# Author: Bohua Zhan

from kernel.type import TFun, TConst, NatType
from kernel.term import Term, Const, Binary
from data.list import ListType, mk_literal_list, is_literal_list, dest_literal_list

"""Utility functions for characters and strings."""

charT = TConst("char")
stringT = TConst("string")

Char = Const("Char", TFun(NatType, charT))
String = Const("String", TFun(ListType(charT), stringT))

def mk_char(c):
    """Given a Python string of length 1, return the corresponding
    HOL character.

    """
    assert isinstance(c, str) and len(c) == 1, "mk_char: expect a string of length 1"
    return Char(Binary(ord(c)))

def mk_string(s):
    """Given a Python string, return the corresponding HOL string."""
    assert isinstance(s, str), "mk_string: expect a string"
    return String(mk_literal_list([mk_char(c) for c in s], charT))

def is_char(t):
    """Whether the given term is a HOL character."""
    assert isinstance(t, Term), "is_char"
    return t.is_comb('Char', 1) and t.arg.is_binary()

def is_string(t):
    """Whether the given term is a HOL string."""
    assert isinstance(t, Term), "is_string"
    return t.is_comb('String', 1) and is_literal_list(t.arg) and \
        all(is_char(c) for c in dest_literal_list(t.arg))

def dest_char(t):
    """Given a HOL character, return the corresponding Python string
    of length 1.

    """
    assert isinstance(t, Term), "dest_char"
    assert t.is_comb('Char', 1) and t.arg.is_binary(), "dest_char"
    return chr(t.arg.dest_binary())

def dest_string(t):
    """Given a HOL string, return the corresponding Python string."""
    assert isinstance(t, Term), "dest_string"
    assert t.is_comb('String', 1) and is_literal_list(t.arg), "dest_string"
    return ''.join(dest_char(c) for c in dest_literal_list(t.arg))
