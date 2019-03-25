# Author: Bohua Zhan

"""Settings for printing."""

settings_stack = [{

    # Whether to print unicode.
    'unicode': False,

    # Whether to print with highlight.
    'highlight': True,

}]

def update_settings(**kargs):
    prev = settings_stack[-1]
    current = prev.copy()
    current.update(**kargs)
    settings_stack.append(current)

def recover_settings():
    settings_stack.pop()

def unicode():
    return settings_stack[-1]['unicode']

def highlight():
    return settings_stack[-1]['highlight']

def with_settings(func):
    """Decorator for functions that accept printer settings.

    This decorator enables the wrapped function to accept keyword
    arguments unicode and highlight. These keyword arguments are
    removed before calling the actual function.

    If at least one keyword argument is in contradiction with the
    current settings_stack, a new setting is pushed onto the
    settings_stack before evaluating the function. The new setting
    is popped from the setting_stack after the return of the
    function, or after any exceptions.

    """
    def wrapper(*args, **kargs):
        # Copy printer settings into separate dictionary, remove
        # from original kargs
        printer_args = dict()
        for k in settings_stack[-1]:
            if k in kargs:
                if kargs[k] != settings_stack[-1][k]:
                    printer_args[k] = kargs[k]
                del kargs[k]
        
        if printer_args:
            try:
                update_settings(**printer_args)
                return func(*args, **kargs)
            finally:
                recover_settings()
        else:
            return func(*args, **kargs)

    return wrapper
