#
# tqft.py
#

# Goal - implement the TQFT invariant coming from ... [REF]

import snappy

from sage.modules.free_module_element import vector
from sage.matrix.constructor import Matrix
from sage.rings.number_field.number_field import CyclotomicField
from sage.arith.misc import gcd

from verbose import verbose_print

# Jones polynomial and related invariants

def Jones_tests(K, name, verbose=3):
    """
    Given a snappy link K and its name, compute the Jones polynomial
    of K.  Then, return the third derivative evaluated at 1, as well
    as the original polynomial evaluated at the 5th root of 1.  Both
    are relevant to obstructing cosmetic surgeries.
    """
    
    if K == None:
        return None, None
        
    if K.DT_code(True) == 'DT[aaaa]':
        # A one-crossing diagram of the unknot. Hard-coded because
        # the code below crashes on the unknot.
        return 1, 0
    
    V = K.jones_polynomial(new_convention=False)
    # The 'new_convention=False' ensures we get classical Jones polynomial
    verbose_print(verbose, 10, [name, V, "Jones polynomial"])
    Q = V.derivative().derivative().derivative()
    
    w = CyclotomicField(5).gen() # so w = exp(2*Pi*I/5)
    # Alternative, more complicated expression below:
    # w = UniversalCyclotomicField().gen(5) 

    verbose_print(verbose, 10, [Q(1), "Jones third derivative at 1"])
    verbose_print(verbose, 10, [V(w), "Jones poly evaluated at exp(2*Pi*I/5)"])
    
    return int(Q(1)), V(w)

def quantum_int(n):
    a = CyclotomicField(10).gen()
    return (a**(2*n) - a**(-2*n))/ (a**(2) - a**(-2))

def tau_five(K, s, verbose=3):
    """
    Given a knot K (as a spherogram link) and a slope s = (m,n) where
    n = 1 or n = 2, returns the quantum invariant tau_5(K(s)). The
    result is correct up to a global scalar, which should be
    sufficient for comparing tau_5(K(s)) to tau5(U(s)), where U is the
    unknot.
    """
    G = CyclotomicField(20)
    z = G.gen()
    a = z**2  # generates CyclotomicField(10)
    delta = a**2 - a**(-2)
    sqrtm5 = 2*z^7 - z^5 + 2*z^3  # sqrt(-5)
    eta = delta/sqrtm5
    # eta = (a^2 - a^-2)/(sqrt(-5))
   
    Id   = Matrix(G, [[1, 0], [0, 1]]) 
    rhoT = Matrix(G, [[1, 0], [0, -a**3]])  # Prop 2.7 of Detcherry
    one  = quantum_int(1)
    two  = quantum_int(2)
    four = quantum_int(4)
    # rhoS = eta * Matrix(G, 2, 2, lambda i, j: (-1)**(i+j+2) * quantum_int((i + 1) * (j + 1)))
    rhoS = eta * Matrix(G, [[one, -two], [-two, four]])  # Prop 2.7 of Detcherry
    # assert rhoS**2 == Id
    # assert rhoT**5 == Id
    # assert (rhoS * rhoT)**3 == Id  # this is only projectively true.
    
    L = euclidean(s) 
    rep = [rhoS, rhoT]
    prod = syllables_to_matrix(L, rep)

    # m, n = s
    # if n == 1:
    #     prod = rhoT**m * rhoS
    # if n == 2:
    #     prod = rhoS**2 * rhoT**((m-1)/2) * rhoS * rhoT**(-2) * rhoS  # ???

    _, u2 = Jones_tests(K, None, verbose = verbose)
    u = vector((1, u2))
    v = prod * vector((1, 0))

    return u.dot_product(v)

def IIS_test(K, s, verbose=3):
    """
    Given a snappy link K, plus a slope s, implement the test of
    Ichihara-Ito-Saito, Theorem 1.2. That is, decide whether (s, -s)
    is definitely not a chirally cosmetic pair. To rule this out, we
    need two things to be true:

    * V_K(exp(2*Pi*I/5) is not real.
    * tau_5(K(s)) != tau_5(U(s)) where U is the unknot.
    """

    _, Jones_fifth = Jones_tests(K, None, verbose = verbose)
    verbose_print(verbose, 5, ['V_K(exp(2*Pi*I/5)', Jones_fifth])    

    tau_five_K = tau_five(K, s, verbose=verbose)
    U = snappy.RationalTangle(1,1).numerator_closure()
    tau_five_U = tau_five(U, s, verbose=verbose)
    
    verbose_print(verbose, 5, ['tau_5(K(s))', tau_five_K])
    verbose_print(verbose, 5, ['tau_5(U(s))', tau_five_U])
    
    return (Jones_fifth != Jones_fifth.conjugate()) and (tau_five_K != tau_five_U)

def euclidean(s):
    """
    Given an integer vector s = (p, q), with g = gcd(p, q), returns
    the lengths of the syllables (of T) in a word in the generators

    S = [0 -1]  T = [1 1]
        [1  0],     [0 1]

    of PSL(2, ZZ) taking (+/- g, 0) to s.  For example, if g = 1 then
    s represents an (unoriented) slope in the torus.  In this case the
    word in S and T gives a mapping class taking the (unoriented)
    meridian (+/- 1, 0) to s.
    
    Example: 

    sage: euclidean((13, 4))                                                   
    [4, 2, 2, 2]

    In detail, we have: 

    13, 4 ---> 13 - 4*4, 4  =  -3, 4 --->    (k = 4)
     4, 3 --->  4 - 2*3, 3  =  -2, 3 --->    (k = 2)
     3, 2 --->  3 - 2*2, 2  =  -1, 2 --->    (k = 2)
     2, 1 --->  2 - 2*1, 1  =   0, 1 --->    (k = 2)
     1, 0

    Thus the desired word in T and S is 
    T^4 * S * T^2 * S * T^2 * S * T^2 * S

    sage: euclidean((-9, 4))                                                   
    [0, 1, 2, 5]

    This time we have: 

    -9, 4 ---> -9 - 0*4, 4  =  -9, 4 --->    (k = 0)
     4, 9 --->  4 - 1*9, 9  =  -5, 9 --->    (k = 1)
     9, 5 --->  9 - 2*5, 5  =  -1, 5 --->    (k = 2)
     5, 1 --->  5 - 5*1, 1  =   0, 1 --->    (k = 5)
     1, 0

    Thus the desired word is: 
    T^0 * S * T^1 * S * T^2 * S * T^5 * S
    """
    p, q = s
    
    # we work in PSL so we can make q non-negative
    if q <= 0:
        p, q = -p, -q

    terms = []
    while q > 0:
        if p < 0:
            k = 0
        else:
            k = (p // q)
            if p % q != 0:
                k = k + 1
        terms.append(k)
        # p, q = p - k*q,  q  # T^-k
        # p, q =       q, -p  # S^-1
        p, q = q, k*q - p
        
    return terms

def syllables_to_matrix(L, rep = None):
    """
    Given syllable lengths L, returns the corresponding matrix in
    SL(2, ZZ).  This "inverts" the function euclidean.

    Example: 

    sage: euclidean((13, 4))
    [4, 2, 2, 2]
    sage: syllables_to_matrix([4, 2, 2, 2])
    [ 13 -10]
    [  4  -3]
    
    sage: euclidean((-9, 4))                                                   
    [0, 1, 2, 5]
    sage: syllables_to_matrix([0, 1, 2, 5])
    [-9  2]
    [ 4 -1]
    """
    if rep == None:
        S  = Matrix(ZZ, [[0, -1], [1, 0]])
        T  = Matrix(ZZ, [[1,  1], [0, 1]])
    else:
        S, T = rep
        
    prod = S.parent().identity_matrix()  # accumulator
    for l in L:
        prod = prod * T**l * S
        
    return prod
