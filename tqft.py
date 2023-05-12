#
# tqft.py
#

# Goal - implement the TQFT invariant coming from ...

import snappy

from sage.modules.free_module_element import vector
from sage.matrix.constructor import Matrix

from sage.rings.number_field.number_field import CyclotomicField
from verbose import verbose_print

# Jones polynomial and related invariants

def Jones_tests(K, name, verbose=3):
    """
    Given a snappy link K and its name, compute the Jones polynomial of K.
    Then, return the third derivative evaluated at 1, as well as 
    the original polynomial evaluated at the 5th root of 1.
    Both are relevant to obstructing cosmetic surgeries.
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
    a5 = CyclotomicField(10).gen()
    return (a5**(2*n) - a5**(-2*n))/ (a5**(2) - a5**(-2))

def tau_five(K, s, verbose=3):
    """
    Given a knot K (as a spherogram link) and
    a slope s = (m,n) where n=1 or n=2, returns the quantum invariant
    tau_5(K(s)). The result is correct up to a global scalar, which should be 
    sufficient for comparing tau_5(K(s)) to tau5(U(s)), where U is the unknot.
    """
    m, n = s
    assert n == 1 or n == 2
    _, u2 = Jones_tests(K, None, verbose = verbose)

    F = CyclotomicField(10)
    a5 = F.gen()
    delta = a5**2 - a5**(-2)
    # eta5 = (a5^2 - a5^-2)/(sqrt(-5)) = delta/(sqrt(-5)) # The
    # calling function is computing a ratio of taus, so we can ignore
    # the global scaling factor of sqrt(-5).
    
    rhoT = Matrix(F, [[1, 0], [0, -a5**3]])
    one = quantum_int(1)
    two = quantum_int(2)
    four= quantum_int(4)
    rhoS = delta * Matrix(F, [[one, -two], [-two, four]])
    # rhoS = eta5 * Matrix(F, [[one, -two], [-two, four]])
    if n == 1:
        prod = rhoT**m * rhoS
    if n == 2:
        prod = rhoS**2 * rhoT**((m-1)/2) * rhoS * rhoT**(-2) * rhoS

    u = vector((1, u2))
    v = prod * vector((1, 0))

    return u.dot_product(v)

def IIS_test(K, s, verbose=3):
    """
    Given a snappy link K, plus a slope s, implement the test of Ichihara-Ito-Saito,
    Theorem 1.2. That is, decide whether (s, -s) is definitely not a chirally
    cosmetic pair. To rule this out, we need two things to be true:
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
    
