"""Type checking at runtime."""

from collections.abc import Iterable

check = True

def checkinstance(*args):
    if not check:
        return

    fname = args[0]

    def check_type(v, T):
        if type(T) == list:
            if not isinstance(v, Iterable):
                raise TypeError('%s expects %s but got %s' % (fname, 'list', str(type(v))))
            for item in v:
                check_type(item, T[0])
        elif not isinstance(v, T):
                raise TypeError('%s expects %s but got %s' % (fname, T, str(type(v))))

    for i in range(len(args) // 2):
        check_type(args[2*i+1], args[2*i+2])
