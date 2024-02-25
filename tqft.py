#
# tqft.py
#

# Goal - implement the TQFT invariant coming from Detcherry.
# This code is currently unreliable, and should not be used.

import snappy

from sage.modules.free_module_element import vector
from sage.matrix.constructor import Matrix
from sage.rings.number_field.number_field import CyclotomicField
from sage.arith.misc import gcd

from verbose import verbose_print

# # Jones polynomial and related invariants
# The routine below can go here, if and when the rest of this code becomes reliable.
# 
# def Jones_tests(K, name, verbose=3):
#     """
#     Given a snappy link K and its name, compute the Jones polynomial
#     V(K), in the original normalization. Then, return the following data:
#     * V'''(1), the Ichihara-Wu invariant
#     * (V'''(1)+3*V''(1))/-36, the Ito invariant (times four)
#     * V(exp(2*Pi*I/5)), the Detcherry invariant  
#     
#     All of these are relevant to obstructing cosmetic surgeries.
#     """
#     
#     if K == None:
#         return None, None
#         
#     V = K.jones_polynomial(new_convention=False)
#     # The 'new_convention=False' ensures we get classical Jones polynomial
#     verbose_print(verbose, 10, [name, V, "Jones polynomial"])
#     P = V.derivative().derivative() # Second derivative
#     Q = V.derivative().derivative().derivative() # Third derivative
#     
#     Ito = int((Q(1)+3*P(1))/(-36)) # 4 times Ito's invariant v_3
#     IchiharaWu = int(Q(1)) # Ichihara-Wu invariant
#     
#     w = CyclotomicField(5).gen() # so w = exp(2*Pi*I/5)
#     Detcherry = V(w)
# 
#     verbose_print(verbose, 10, [IchiharaWu, "Jones third derivative at 1"])
#     verbose_print(verbose, 10, [Ito, "Four times Ito invariant v_3"])
#     verbose_print(verbose, 10, [Detcherry, "Jones poly evaluated at exp(2*Pi*I/5)"])
#     
#     return IchiharaWu, Ito, Detcherry

def quantum_int(n):
    """
    Given an integer n, returns the quantum integer [n],
    where a = exp(2*pi*i /10)
    """
    
    a = CyclotomicField(10).gen()
    return (a**(2*n) - a**(-2*n))/ (a**(2) - a**(-2))


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
    Given syllable lengths L, returns the corresponding matrix in SL(2,
    ZZ).  This "inverts" the function euclidean.  (If rep is not none,
    then uses the given representation of SL(2, ZZ) instead of the
    standard one.)

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
    sqrtm5 = 2*z**7 - z**5 + 2*z**3  # sqrt(-5)
    eta = delta/sqrtm5 # Detcherry, displayed equation above Thm 2.3
   
    Id   = Matrix(G, [[1, 0], [0, 1]]) 
    T = Matrix(G, [[1, 0], [0, -a**3]])  # Prop 2.7 of Detcherry
    one  = quantum_int(1)
    two  = quantum_int(2)
    four = quantum_int(4)
    # S = eta * Matrix(G, 2, 2, lambda i, j: (-1)**(i+j+2) * quantum_int((i + 1) * (j + 1)))
    S = eta * Matrix(G, [[one, -two], [-two, four]])  # Prop 2.7 of Detcherry
    # assert S**2 == Id
    # assert T**5 == Id
    # assert (S * T)**3 == Id  # this is only projectively true.
    
    L = euclidean(s) 
    rep = [S, T]
    prod = syllables_to_matrix(L, rep)

    # m, n = s
    # if n == 1:
    #     prod = T**m * S
    # if n == 2:
    #     prod = S**2 * T**((m-1)/2) * S * T**(-2) * S  # ???  Is this the inverse?

    _, _, Jones_fifth = Jones_tests(K, None, verbose = verbose)
    u = vector((1, Jones_fifth))
    v = prod * vector((1, 0))

    return u.dot_product(v)

def tau_distinguishes(K, s, verbose=3):
    """
    Given a snappy link K, plus a slope s, implement implement 
    the test of Ichihara-Ito-Saito, Theorem 1.2. The test has two parts:
    
    * Decide whether V_K(exp(2*Pi*I/5) is a non-real number.
      If real, return False (the test fails).
    * Decide whether tau_5(K(s)) != tau_5(U(s)) where U is the unknot.
    
    (For the second test, one could reduce the entries of s mod 5,
    because the quantum representation in Proposition 2.7 of Detcherry 
    only cares about the matrix over Z/5Z.) 
    
    If both parts of the test succeed, then (s, -s) cannot be a chirally
    cosmetic pair.
    """

    _, _, Jones_fifth = Jones_tests(K, None, verbose = verbose)
    verbose_print(verbose, 5, ['V_K(exp(2*Pi*I/5):', Jones_fifth])
    
    tau_five_K = tau_five(K, s, verbose=verbose)
    U = snappy.RationalTangle(1,1).numerator_closure()
    tau_five_U = tau_five(U, s, verbose=verbose)
    
    verbose_print(verbose, 5, ['s:', s, 'tau_5(K(s)):', tau_five_K])
    verbose_print(verbose, 5, ['s:', s, 'tau_5(U(s)):', tau_five_U])
    
    return (Jones_fifth != Jones_fifth.conjugate()) and (tau_five_K != tau_five_U)


def IIS_test(K, verbose=3):
    """
    Given a snappy link K, implement implement the test of
    Ichihara-Ito-Saito, Theorem 1.2. The test has two parts:
    
    * Decide whether V_K(exp(2*Pi*I/5) is a non-real number.
      If real, return False (the test fails).
    * For every possible primitive pair s = (m,n) with entries modulo 5,
      decide whether tau_5(K(s)) != tau_5(U(s)) where U is the unknot.
    
    It suffices to take (m mod 5, n mod 5) because the quantum representation
    in Proposition 2.7 of Detcherry only cares about the matrix over Z/5Z.
    
    If both of the bulleted tests are True, then K cannot admit any chirally
    cosmetic pairs of 0-type. That is, (s,-s) is never a chirally cosmetic pair.
    
    NOTE: THIS WILL NEVER SUCCEED. Since K(1,0) = U(1,0) = S^3, and tau_5 only
    cares about coordinates mod 5, we get tau_5(K(6,5)) = tau_5(U(6,5)) always.
    """
            
    for m in range(0,5):
        for n in range(0,5):
            s = (m,n)
            if s == (0,0):
                continue
            if not tau_distinguishes(K, s, verbose):
                return False
    
    return True
   