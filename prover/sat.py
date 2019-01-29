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
    for clause in cnf:
        L=len(clause)
        #cnf contains the empty set    
        if L==0:                                        
            return('inconsistentCNF')                            
        
        #change [('x',False)]to ~x ,change [('x',True)]to x   
        for literal in clause:
            if literal[1]==False:                       
                literal_new='~'+literal[0]                      
            elif literal[1]==True:                      
                literal_new=literal[0]                          
            clause[clause.index(literal)]=literal_new           
        if L==1:
            cnf[cnf.index(clause)]=clause[0]    
        #turn literals to clause by adding (,|,)                     
        elif L>=2:                                      
            c="("+clause[0]
            for i in range(1,L):
                c=c+" | "+clause[i]
            cnf[cnf.index(clause)]=c+")"                        
        
    if len(cnf)==1:
        #when the cnf has only one clause,remove the brackets
        if cnf[0][0]=='(':
            new_cnf=cnf[0][1:len(cnf[0][0])-2]
            return(new_cnf)                             
        else:
            return(cnf[0])
        
    elif len(cnf)>=2:
        new_cnf=cnf[0]
        for j in range(1,len(cnf)):
            new_cnf=new_cnf+" & "+cnf[j]
        return(new_cnf)



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
        if len(clause)==0:                               
            return(False)
            
        for literal in clause:
            #inst doesn't contain assignment for all variables
            if not literal[0] in inst:                                 
                raise SATSolverException
            s=0
            #the literal is assigned True,so the clause is satisfiable
            if inst[literal[0]]-literal[1]==0:           
                s=1
                break
        #all literals in the clause is assigned False
        if s==0:
            return(False)                                
    #all clause in the cnf is satisfiable
    return(True)     



def bucket(cnf):
    '''create a bucket Bx for each variable x'''
    Buckets={}
    for clause in cnf:
        for (a,b) in clause:
            if not a in Buckets:
                Buckets[a]=[cnf.index(clause)]
            else:
                Buckets[a].append(cnf.index(clause))
    return(Buckets)
    


def replace(cnf,x,y):
    """
    Replacing evering occurrence of variable x
    x is a variable, y is True or False
    """
    cnf_new=[]
    for clause in cnf:
        if_add_clause=1
        for (a,b) in clause:
            
            #delete the cnf
            if a==x and ((b==True and y==True)or(b==False and y==False)):
                if_add_clause=0
                break
            #delete the literal
            elif a==x and ((b==True and y==False)or(b==False and y==True)):
                del clause[clause.index((a,b))]
        if if_add_clause==1:    
            cnf_new.append(clause)
    return(cnf_new)



def solve_cnf(cnf):
    """Solve the given CNF.
    
    If the CNF is satisfiable, returns the satisfying assignment
    as a dictionary.
    
    Otherwise, return None.
    
    """
    res={}
    buc=bucket(cnf)
    
    #empty set
    if len(cnf)==0:
        return(res)
    
    #cnf contains the empty set
    for clause in cnf:
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
            cnf_new=replace(cnf,x,res[x])            
            if solve_cnf(cnf_new)!=None:
                return dict(res,**solve_cnf(cnf_new))
            else:
                return None
                
    #unit resolution
    for clause in cnf:
        if len(clause)==1:
            #when the clause is [('x',True)],assigned x True;when the clause is [('x',False)],assigned x False;   
            res[clause[0][0]]=clause[0][1]
            cnf_new=replace(cnf,clause[0][0],clause[0][1])
            if solve_cnf(cnf_new)!=None:
                return dict(res,**solve_cnf(cnf_new))
            else:
                return None
    
    #assume a variable's value,here we choose the first variable appears in the cnf
    m=cnf[0][0][0]
    cnf_new1=replace(cnf,m,True)
    cnf_new2=replace(cnf,m,False)
    if solve_cnf(cnf_new1)!=None:
        res[m]=True
        return dict(res,**solve_cnf(cnf_new1))
    elif solve_cnf(cnf_new2)!=None:
        res[m]=False
        return dict(res,**solve_cnf(cnf_new2))
    else:
        return None
