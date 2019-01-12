# Author: Bohua Zhan

"""Global settings. Mainly for printing."""

settings_stack = [{

    # Function for printing terms.
    'term_printer': None,

    # Whether to print type for bound variables.
    'print_abs_type': False,

    # Whether to print unicode.
    'unicode': False,

    # Whether to print with highlight.
    'highlight': False,

}]

def update_settings(**kargs):
    prev = settings_stack[-1]
    current = prev.copy()
    current.update(**kargs)
    settings_stack.append(current)

def recover_settings():
    settings_stack.pop()

def term_printer():
    return settings_stack[-1]['term_printer']

def print_abs_type():
    return settings_stack[-1]['print_abs_type']

def unicode():
    return settings_stack[-1]['unicode']

def highlight():
    return settings_stack[-1]['highlight']
