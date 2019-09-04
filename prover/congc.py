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

        return "Pending:\n" + pending + "\nrep:\n" + rep + "\nclass_list:\n" + class_list + \
            "\nuse_list\n" + use_list + "\nlookup\n" + lookup

    def add_var(self, s):
        """Add new variable."""
        assert isinstance(s, str)
        if s not in self.rep:
            self.rep[s] = s
            self.class_list[s] = [s]
            self.use_list[s] = []

    def merge(self, s, t):
        """Merge terms s and t. s must be either a string or a pair
        of strings (for f(s1, s2)). t must be a string.

        """
        assert isinstance(t, str)
        self.add_var(t)
        if isinstance(s, str):
            self.add_var(s)
            self.pending.put((PENDING_CONST, s, t))
            self.propagate()
        else:
            a1, a2 = s
            assert isinstance(a1, str) and isinstance(a2, str)
            self.add_var(a1)
            self.add_var(a2)
            rep_a1, rep_a2 = self.rep[a1], self.rep[a2]
            if (rep_a1, rep_a2) in self.lookup:
                eq2 = self.lookup[(rep_a1, rep_a2)]
                self.pending.put((PENDING_COMB, (s, t), eq2))
                self.propagate()
            else:
                self.lookup[(rep_a1, rep_a2)] = (s, t)
                self.use_list[rep_a1].append((s, t))
                self.use_list[rep_a2].append((s, t))

    def propagate(self):
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
                    rep_a, rep_b = rep_b, rep_a

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

    def normalize(self, t):
        """Normalize a term t. This time, it can be in arbitrarily
        nested form.

        """
        if isinstance(t, str):
            return self.rep[t]
        else:
            t1, t2 = t
            u1 = self.normalize(t1)
            u2 = self.normalize(t2)
            if isinstance(u1, str) and isinstance(u2, str):
                if (u1, u2) in self.lookup:
                    _, a = self.lookup[(u1, u2)]
                    return self.rep[a]
                else:
                    return (u1, u2)

    def test(self, t1, t2):
        """Test whether t1 is equal to t2."""
        u1 = self.normalize(t1)
        u2 = self.normalize(t2)
        return u1 == u2


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
