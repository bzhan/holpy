from prover import tseitin
from kernel.type import BoolType
from kernel.term import Var, Not, Or, And, Eq
from kernel.theory import register_macro
from logic import matcher
from kernel.proofterm import ProofTerm
from logic.logic import resolution, apply_theorem, imp_disj_iff
from logic.conv import rewr_conv, bottom_conv, top_conv, try_conv, Conv, ConvException
from kernel.macro import Macro
import subprocess
import re
from math import floor

def get_atom(tm):
    """tm is a literal, return the var."""
    assert tm.is_var() and tm.T == BoolType or tm.is_not(), "Invalid term: %s" % str(tm)
    return tm if tm.is_var() else tm.arg

def is_cnf(cnf):
    if not cnf.is_conj():
        return False
    clauses = cnf.strip_conj()
    for clause in clauses:
        if not clause.is_disj():
            return False
        literals = clause.strip_disj()
        for lit in literals:
            if not (lit.is_var() and lit.get_type() == BoolType) and not lit.is_not():
                return False
    
    return True

class replace_conv(Conv):
    def __init__(self, pt):
        self.pt = pt

    def get_proof_term(self, t):
        if t == self.pt.prop.lhs:
            return self.pt
        else:
            raise ConvException

@register_macro('disj_force')
class DisjForceMacro(Macro):
    def __init__(self):
        self.level = 1
        self.limit = None
        
    def get_proof_term(self, prevs, goal_lit):
        disj, *lit_pts = prevs
        pt_conj = lit_pts[0]

        for i in range(len(lit_pts)):
            pt = lit_pts[i]
            if not pt.prop.is_not():
                lit_pts[i] = pt.on_prop(rewr_conv('double_neg', sym=True))

        def conj_right_assoc(pts):
            """
            Give a sequence of proof terms: ⊢ A, ⊢ B, ⊢ C,
            return ⊢ A ∧ (B ∧ C)
            """
            if len(pts) == 1:
                return pts[0]
            else:
                return apply_theorem('conjI', pts[0], conj_right_assoc(pts[1:]))

        # get a /\ b /\ c
        pt_conj = conj_right_assoc(lit_pts)
        
        other_lits = [l.prop.arg if l.prop.is_not() else Not(l.prop) for l in lit_pts]
        
        # use de Morgan
        pt_conj1 = pt_conj.on_prop(bottom_conv(rewr_conv('de_morgan_thm2', sym=True)))
        
        # if len(other_lits) == 1 and other_lits[0].is_not():
        #     pt_conj1 = pt_conj.on_prop(rewr_conv('double_neg', sym=True))

        # Equality for two disjunctions which literals are the same, but order is different.
        eq_pt = imp_disj_iff(Eq(disj.prop, Or(goal_lit, *other_lits)))
        new_disj_pt = disj.on_prop(top_conv(replace_conv(eq_pt)))

        # A \/ B --> ~B --> A
        pt = ProofTerm.theorem('force_disj_true1')
        A, B = pt.prop.strip_implies()[0]
        C = pt.prop.strip_implies()[1]

        inst1 = matcher.first_order_match(C, goal_lit)
        inst2 = matcher.first_order_match(A, Or(goal_lit, *other_lits), inst=inst1)
        inst3 = matcher.first_order_match(B, pt_conj1.prop, inst=inst2)
        pt_implies = apply_theorem('force_disj_true1', new_disj_pt, pt_conj1, inst=inst3)
        
        return pt_implies.on_prop(try_conv(rewr_conv('double_neg')))

@register_macro('disj_false')
class DisjFalseMacro(Macro):
    def __init__(self):
        self.level = 1
        self.limit = None

    def get_proof_term(self, disj_pt, prevs):
        prev_eq_pt = []
        for pt in prevs:
            if not pt.prop.is_not():
                pt_true = pt.on_prop(rewr_conv('eq_true'))
            else:
                pt_true = pt.on_prop(rewr_conv('eq_false'))
            prev_eq_pt.append(pt_true)

        new_disj_pt = disj_pt
        for pt in prev_eq_pt:
            new_disj_pt = new_disj_pt.on_prop(bottom_conv(replace_conv(pt)), bottom_conv(rewr_conv('not_true')))
        return new_disj_pt.on_prop(bottom_conv(rewr_conv('disj_false')))
        

def read_cnf_file(cnf_file):
    """Read a cnf file and construct the cnf tuple"""
    assert cnf_file.endswith('.cnf'), "Illegal file format."
    with open(cnf_file, 'r') as f:
        lines = [l for l in f.readlines() if not l.startswith('c')]
        base_info = lines[0].split(' ')
        var_num = int(base_info[2])
        clause_num = int(base_info[3][:-1])
        disjs = []
        for l in lines[1:]:
            lits = list(filter(None, re.split(r'(?:\t|\n|\s)\s*', l)))
            t = []
            for lit in lits[:-1]:
                l = int(lit)
                if l > 0:
                    t.append(('y'+str(l), True))
                else:
                    t.append(('y'+str(-l), False))
            disjs.append(tuple(t))

        return tuple(disjs)   

def convert_cnf_to_HOL(cnf_file):
    disjs = read_cnf_file(cnf_file)
    tms = []
    for disj in disjs:
        lits = []
        for var, stat in disj:
            if stat:
                lits.append(Var(var, BoolType))
            else:
                lits.append(Not(Var(var, BoolType)))
        tms.append(Or(*lits))
     
    return And(*tms)


class ProofTrace:
    pass

class Resolvent(ProofTrace):
    """Represent the first section element in proof trace."""
    def __init__(self, s):
        assert s.startswith('CL'), '%s is not a resolvent.' % s
        self.s = s
        elem = re.split(r'(?:CL:\s|\s<=\s|\s)\s*', s)
        elem = list(filter(None,elem))
        self.id = int(elem[0])
        self.rsl = tuple(int(i) for i in elem[1:])

    def __str__(self):
        return self.s

class ImpliedVarValue(ProofTrace):
    """Represent the second section element in proof trace."""
    def __init__(self, s):
        assert s.startswith('VAR')
        self.s = s
        elem = re.split(r'(?:VAR:|L:|V:|A:|Lits:|\s)\s*', s)
        elem = list(filter(None, elem))
        elem = [int(e) for e in elem]
        self.var, self.level, self.value, self.act, *self.lits = elem

    def __str__(self):
        return self.s

class Conflict(ProofTrace):
    """Represent the clause in which all literals are evaluated to false."""
    def __init__(self, s):
        assert s.startswith('CONF')
        self.s = s
        elem = [int(e) for e in list(filter(None, re.split(r'(?:CONF:|\s==\s|\s)\s*', s)))]
        self.cls = elem[0]
        self.lits = elem[1:]

    def __str__(self):
        return self.s
        

class zChaff:
    """Data structure for cnf term."""
    def __init__(self, t):
        assert tseitin.is_logical(t), "%s is not a logical term." % str(t)        
        if not is_cnf(t):
            self.encode_pt = tseitin.encode(t)
        else:
            self.encode_pt = ProofTerm.assume(t)
        self.f = self.encode_pt.prop

        # Index the vars occur in cnf term 
        self.vars = set()
        self.var_index = dict()
        self.index_var = dict()
        cnf_list = []
        clauses = self.f.strip_conj()
        i = 1

        for clause in clauses:
            literals = clause.strip_disj()
            c = []
            for lit in literals:
                atom = get_atom(lit)
                if atom not in self.var_index:
                    self.var_index[atom] = i
                    self.index_var[i] = atom
                    i += 1
                index = self.var_index[atom]
                if atom != lit:
                    c.append(-index)
                else:
                    c.append(index)
            cnf_list.append(tuple(c))

        self.cnf_list = tuple(cnf_list)

        # Indicate the cnf is whether SAT 
        self.state = None

        # Dictionary from index to clause
        self.clause_pt = {i : ProofTerm.assume(c) for i, c in enumerate(self.f.strip_conj())}

        self.conflict_pt = None

    def __str__(self):
        return str(self.f)

    def __eq__(self, others):
        return self.f == others.f

    @property
    def var_num(self):
        return len(self.var_index)

    @property
    def clause_num(self):
        return len(self.cnf_list)

    def solve(self):
        """
        Call zChaff solver, return the proof term.
        """
        # First write the cnf to a .cnf file.
        s = 'p cnf ' + str(self.var_num) + ' ' + str(self.clause_num)
        for clause in self.cnf_list:
            s += '\n' + ' '.join(str(l) for l in clause) + ' 0'
        with open('./sat/x.cnf', 'w') as f:
            f.write(s)

        # then call zChaff to get the proof trace
        p = subprocess.Popen('.\\sat\\binaries\\zchaff.exe .\\sat\\x.cnf', 
                stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        stdout, stderr = p.communicate()
        result = stdout.decode('utf-8').split('\n')[-2]
        assert result == "RESULT:\tUNSAT\r"

        # proof reconstruct 
        first = []
        second = []
        third = []
        with open('.\\resolve_trace', 'r') as f:
            lines = f.readlines()
            for l in lines:
                if l.startswith('CL'):
                    first.append(Resolvent(l))
                elif l.startswith('VAR'):
                    second.append(ImpliedVarValue(l))
                else:
                    third.append(Conflict(l))
                
        for j, f in enumerate(first):
            res_cls = f.rsl
            pt = self.clause_pt[res_cls[0]]
            for i in range(len(res_cls)-1):
                pt = resolution(pt, self.clause_pt[res_cls[i+1]])
            self.clause_pt[len(self.clause_pt)] = pt

        second = sorted(second, key=lambda x: x.level)
        
        # dictionary from var index to its true value
        var_pt = {}
        for s in second:
            cls_pt = self.clause_pt[s.act]
            pts = []
            lits = [floor(l/2) for l in s.lits if floor(l/2) != s.var]
            if not lits:
                var_pt[s.var] = cls_pt
                continue
            exist_var_pt = [var_pt[l] for l in lits]
            exact_var = self.index_var[s.var] if s.value == 1 else Not(self.index_var[s.var])
            prevs = [cls_pt] + exist_var_pt
            var_pt[s.var] = DisjForceMacro().get_proof_term(prevs, exact_var)

        conflict_cls = third[0]
        literal_pt = [var_pt[floor(i/2)] for i in conflict_cls.lits]
        self.conflict_pt = DisjFalseMacro().get_proof_term(self.clause_pt[conflict_cls.cls], literal_pt)    

        # return the theorem
        pt1, pt2 = self.encode_pt, self.conflict_pt
        while pt1.prop.is_conj():
            pt_left = apply_theorem('conjD1', pt1)
            pt2 = pt2.implies_intr(pt_left.prop).implies_elim(pt_left)  # remove one clause from assumption
            pt1 = apply_theorem('conjD2', pt1)
        pt2 = pt2.implies_intr(pt1.prop).implies_elim(pt1)  # remove last clause from assumption

        # Clear definition of new variables from antecedent
        eqs = [t for t in pt2.hyps if t.is_equals()]
        eqs = list(reversed(sorted(eqs, key=lambda t: int(t.lhs().name[1:]))))

        for eq in eqs:
            pt2 = pt2.implies_intr(eq).forall_intr(eq.lhs).forall_elim(eq.rhs) \
                    .implies_elim(ProofTerm.reflexive(eq.rhs))

        return apply_theorem('negI', pt2.implies_intr(pt2.hyps[0])).on_prop(rewr_conv('double_neg'))                