#
# tqft.py
#

# Goal - implement the TQFT invariant coming from ...

from sage.rings.number_field.number_field import CyclotomicField
from verbose import verbose_print

# Jones polynomial and related invariants

def Jones_tests(K, name, verbose=3):
    """
    Given a snappy link K and its name (for bookkeeping), 
    compute the Jones polynomial of K.
    Then, return the third derivative evaluated at 1, as well as 
    the original polynomial evaluated at the 5th root of 1.
    Both are relevant to obstructing cosmetic surgeries.
    """
    
    if K == None:
        return None, None
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



