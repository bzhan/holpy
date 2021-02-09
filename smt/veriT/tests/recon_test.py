"""
Test proof reconstruction using veriT solver.
"""
import unittest
from smt.veriT import interface
from contextlib import redirect_stdout
import os
from pathlib import Path


def split_file_name(file_name):
    """f is a full file path, substituting '/' by '_',
    """
    print("file_name: ", file_name)
    print("split_file_name: ", "_".join(file_name.replace(":", "").split("/"))[:-4] + "txt")
    return "_".join(file_name.replace(":", "").split("/"))[:-4] + "txt"

def make_log_folder():
    """Make a folder named 'log'."""
    if not os.path.exists("./smt/veriT/log"):
        os.makedirs("./smt/veriT/log")

def test_single_file(file_name):
    """
    Given a smt file, use veriT to solve it, if it returns
    "SAT", just print "SAT" into the proof file, or else print the 
    proof reconstruction steps into proof file. 
    """
    make_log_folder()
    with open("./smt/veriT/log/"+split_file_name(file_name), "a+") as f:
        with redirect_stdout(f):
            interface.proof_rec(file_name)

def test_folder(folder_path):
    """
    Given a folder, find all files ending with ".smt2", 
    """
    if not os.path.exists(folder_path):
        print("%s does not exist." % folder_path)
    file_names = Path(folder_path).rglob("*.smt2")
    for f in file_names:
        test_single_file(str(f).replace("\\", "/"))