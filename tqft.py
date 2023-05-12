#
# tqft.py
#

# Goal - implement the TQFT invariant coming from ...

from sage.modules.free_module_element import vector
from sage.matrix.constructor import Matrix

from sage.rings.number_field.number_field import CyclotomicField
from verbose import verbose_print

# Jones polynomial and related invariants

def Jones_tests(K, verbose=3):
    """
    Given a snappy link K compute the Jones polynomial of K.
    Then, return the third derivative evaluated at 1, as well as 
    the original polynomial evaluated at the 5th root of 1.
    Both are relevant to obstructing cosmetic surgeries.
    """
    
    if K == None:
        return None, None
    V = K.jones_polynomial(new_convention=False)
    # The 'new_convention=False' ensures we get classical Jones polynomial
    verbose_print(verbose, 10, [K.name(), V, "Jones polynomial"])
    Q = V.derivative().derivative().derivative()
    
    w = CyclotomicField(5).gen() # so w = exp(2*Pi*I/5)
    # Alternative, more complicated expression below:
    # w = UniversalCyclotomicField().gen(5) 

    verbose_print(verbose, 10, [Q(1), "Jones third derivative at 1"])
    verbose_print(verbose, 10, [V(w), "Jones poly evaluated at exp(2*Pi*I/5)"])
    
    return int(Q(1)), V(w)

def quantum_int(n):
    F.<a5> = CyclotomicField(10)
    return (a5^(2*n) - a5^(-2*n))/ (a5^(2) - a5^(-2))

def tau_five(K, s, verbose=3):
    """
    Given a knot K (as a snappy manifold with the correct framing) and
    a slope s (of the form m/2) returns the quantum invariant
    tau_5(K(s)) (up to a global scalar).
    """
    m, n = s
    assert n == 2
    _, u2 = Jones_tests(K, verbose = verbose)

    F.<a5> = CyclotomicField(10)
    delta = a5^2 - a5^-2
    # eta5 = (a5^2 - a5^-2)/(sqrt(-5)) = delta/(sqrt(-5)) # The
    # calling function is computing a ratio of taus, so we can ignore
    # the global scaling factor of sqrt(-5).
    
    rhoT = Matrix(F, [[1, 0], [0, -a5^3]])
    # rhoT = eta5 * Matrix(F, [[1,  1], [0, 1]])
    one = quantum_int(1)
    two = quantum_int(2)
    four= quantum_int(4)
    rhoS = delta * Matrix(F, [[one, -two], [-two, four]])
    prod = rhoS^2 * rhoT^m * rhoS * rhoT^-2 * rhoS

    u = vector((1, u2))
    v = prod * vector((1, 0))

    return u.dot_product(v)

