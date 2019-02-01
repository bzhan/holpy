"""
Implementation of SAT solver.

CNFs are represented using lists of lists of literals, where
each literal is given by a pair (x, b), where x is a string
(name of the boolean variable), and b is a boolean value giving
the sign of the literal.

For example, (~x | y) & (~y | z) is represented as
[[('x', False), ('y', True)], [('y', False), ('z', True)]].

"""

class SATSolverException(Exception):
    pass


def display_cnf(cnf):
    """Display the given CNF."""
    
    if len(cnf)==0:
        return('empty set')                            
    for num_c,clause in enumerate(cnf):
        L=len(clause)
        #cnf contains the empty set    
        if L==0:                                        
            return('inconsistentCNF')                            
        
        #change [('x',False)]to ~x ,change [('x',True)]to x   
        for num_l,(a,b) in enumerate(clause):
            if not b:                       
                literal='~'+a                    
            elif b:                      
                literal=a                         
            clause[num_l]=literal           
          
        #turn literals to clause by adding (,|,)
        cnf[num_c]=' | '.join(clause)
        if len(cnf)==1:
            return(cnf[num_c])
        if L>=2:
            cnf[num_c]='('+cnf[num_c]+')'

    return(' & '.join(cnf))



def is_solution(cnf, inst):
    """Determines whether the given instantiation is a solution to
    the CNF.
    
    inst is a dictionary representing the satisfying assignment. It
    must contain assignment for all variables.
    
    Raises SATSolverException if inst does not contain assignment
    for some variable.
    
    """
    if len(cnf)==0:    
        return(True)
    
    for clause in cnf: 
        if clause==None:
            continue
        
        if len(clause)==0:                               
            return(False)
            
        for (a,b) in clause:
            #inst doesn't contain assignment for all variables
            if not a in inst:                                 
                raise SATSolverException
            val_cnf=0
            #the literal is assigned True,so the clause is satisfiable
            if  inst[a]-b==0:           
                val_cnf=1
                break
        #all literals in the clause is assigned False
        if val_cnf==0:
            return(False)                                
    #all clause in the cnf is satisfiable
    return(True)     



def bucket(cnf):
    '''create a bucket Bx for each variable x'''
    Buckets={}
    for num_c, clause in enumerate(cnf):
        for (a,b) in clause:
            if not a in Buckets:
                Buckets[a]=[num_c]
            else:
                Buckets[a].append(num_c)
    return(Buckets)
    


def replace(cnf,x,y,buc):
    """
    Replacing evering occurrence of variable x
    x is a variable, y is a boolean variable
    """
    for num_c in buc[x]:
        clause_new=[]
        if cnf[num_c]==None:
            continue
        
        for num_l, (a,b) in enumerate(cnf[num_c]):
            
            #delete the cnf
            if a==x and b==y:
                clause_new=None
                break
            #delete the literal assigned False
            elif a!=x:
                clause_new.append((a,b))
            else:
                break
        cnf[num_c]=clause_new
    
    return(cnf)



def solve_cnf(cnf):
    """Solve the given CNF.
    
    If the CNF is satisfiable, returns the satisfying assignment
    as a dictionary.
    
    Otherwise, return None.
    
    """
    res={}
    buc=bucket(cnf)
    res_new=solve_cnf_rec(cnf,buc,res)
    #assign the unassigned variables
    if res_new!=None:
        for x in buc:
            if not x in res_new:
                res_new[x]=True
    return(res_new)
 
def solve_cnf_rec(cnf,buc,res):    
    #empty set
    if len(cnf)==0:
        return(res)
    
    #empty set(only has None clause)
    is_empty_set=1
    for clause in cnf:
        if clause!=None:
            is_empty_set=0
            break
    if is_empty_set==1:
        return(res)
    
    
    #cnf contains the empty set
    for clause in cnf:
        if clause==None:
            continue    
        if len(clause)==0:
            return None
    
    #x only appears in one clause
    for x in buc:
        if len(buc[x])==1:
            for (a,b) in cnf[buc[x][0]]:
                #when b is True,x is assigned True; when b is False,x is assigned False
                if a==x:
                    res[x]=b
                    break
            cnf_new=replace(cnf,x,res[x],buc)
            del buc[x]
            if solve_cnf_rec(cnf_new,buc,res)!=None:
                return dict(res,**solve_cnf_rec(cnf_new,buc,res))
            else:
                return None
                
    #unit resolution
    for clause in cnf:
        if clause==None:
            continue
        if len(clause)==1:
            #when the clause is [('x',True)],assigned x True;when the clause is [('x',False)],assigned x False;   
            res[clause[0][0]]=clause[0][1]
            cnf_new=replace(cnf,clause[0][0],clause[0][1],buc)
            del buc[clause[0][0]]
            if solve_cnf_rec(cnf_new,buc,res)!=None:
                return dict(res,**solve_cnf_rec(cnf_new,buc,rec))
            else:
                return None
    
    #assume a variable's value,here we choose the first variable appears in the cnf
    m=cnf[0][0][0]
    cnf_new1=replace(cnf,m,True,buc)
    cnf_new2=replace(cnf,m,False,buc)
    del buc[x]
    if solve_cnf_rec(cnf_new1,buc,res)!=None:
        res[m]=True
        return dict(res,**solve_cnf_rec(cnf_new1,buc,res))
    elif solve_cnf_rec(cnf_new2,buc,res)!=None:
        res[m]=False
        return dict(res,**solve_cnf(cnf_new2,buc,res))
    else:
        return None