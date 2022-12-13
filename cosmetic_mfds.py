#
# cosmetic_mfds.py
#

# Rule out cosmetic surgeries on one-cusp hyperbolic three-manifolds

# Complication - we need orientation sensitive invariants for the
# resulting filled manifolds.  In the hyperbolic case we can use the
# Chern-Simons invariant.  What do we do in the non-hyperbolic case?
# Worry about the latter...  Does Reidemeister torsion work?  Other
# torsions?


# Imports 


# Division in scripts running under sage is python division.  So we
# need to fix it as follows.  
from __future__ import division
# fixed in SAGE 9.2!  But check this... 

import snappy
import regina
import dunfield
import geom_tests
import fundamental

from verbose import verbose_print

from sage.rings.rational_field import QQ
from sage.functions.other import sqrt, ceil, floor
from sage.symbolic.constants import pi
from sage.arith.misc import gcd, xgcd, factor
from sage.functions.trig import arctan
from sage.rings.real_mpfi import RealIntervalFieldElement
from sage.rings.real_mpfi import RIF
from sage.rings.real_mpfi import RealIntervalField
from sage.misc.functional import det
from sage.modules.free_module_element import vector


# coding


def add_to_dict_of_sets(dictionary, key, value):
    if key not in dictionary:
        dictionary[key] = set([value])
    else:
        dictionary[key].add(value)
    return None


# Names - parsing regina names


def is_lens_space_from_name(name, verbose=3):
    """
    Given a regina name, parses it enough to decide if it is a lens
    space and then extracts the coefficients.  
    
    For our purposes, S2 x S1 is treated as a non-lens space.
    """

    verbose_print(verbose, 15, ["Entering is_lens_space_from_name"])
    if name == None:
        return (None, None)
        
    if name == "S3":
        return (True, [1, 0])
    if name == "RP3":
        return (True, [2, 1])
    # New convention: S2 x S1 is not a lens space.
    # if name == "S2 x S1":
    #     return (True, [0, 1])
        
    # If "L(" appears in the string, then we have a lens space
    # summand.  If "#" does not appear, then we are just a lens space,
    # so we will win.
    if (not "L(" in name) or ("#" in name):
        return (None, None)
    parts = name.split(",")
    assert len(parts) == 2
    parts = [part.strip("L") for part in parts]
    parts = [part.strip("(") for part in parts]
    parts = [part.strip(")") for part in parts]
    ints = [int(part) for part in parts]
    
    verbose_print(verbose, 10, ['Found lens space data:', ints])
    return (True, ints)


def euler_num(coeffs, ModOne = False):
    """
    Given a vector of coefficients of singular fibers in a SFS,
    computes the Euler number.
    If the ModOne flag is True, then reduce the Euler number modulo 1.
    """
    eul = sum( QQ((q, p)) for (p, q) in coeffs )
    if ModOne:
        return eul - floor(eul)
    else:
        return eul
        
        
def euler_char(starting_char, coeffs):
    """
    Computes the Euler characteristic of the base orbifold in a
    Seifert fibration.
    starting_char is the Euler characteristic of the total space of the base
    (ignoring singular fibers). coeffs is the vector of coefficients.
    """
    return starting_char - sum( 1- QQ((1, p)) for (p, q) in coeffs )


def is_closed_sfs_from_name(name, verbose=3):
    """
    Given a regina name, decides whether it is a closed
    SFS, where the base is one of S2, RP2, T (torus),
    or KB (Klein bottle).
    We do not look for larger base surfaces.
    Returns a tuple (found, geometry, base, coeffs).
    * found is True or None.
    * geometry is one of ["Lens", "Elliptic", "S2 x R", "Nil", "Euclidean", "PSL2R", "H2 x R"].
    * base is the total space of the base orbifold
    * coeffs is a tuple of integer coefficients for singular fibers
    
    We artificially split out lens spaces from other elliptic manifolds,
    because their Seifert fibrations are highly non-unique.
    All other closed SFS have at most two Seifert structures, and we pick out
    a preferred one (the one with orientable base).
    
    References: 
    Hatcher, "Notes on basic 3-manifold theory," Theorem 2.3.
    Scott, "The geometries of 3-manifolds"
    
    If M is not recognized as a closed SFS in this way, return
    (None, None, None, None).
    """
        
    verbose_print(verbose, 15, ["Entering is_closed_sfs_from_name"])

    # First, test for S2 x R structures.
    if name == "S2 x S1":
        return (True, "S2 x R", "S2", [])
    if name == "RP3 # RP3":
        return (True, "S2 x R", "RP2", [])

    # Next, test for lens space structures.
    is_lens, lens_coeffs = is_lens_space_from_name(name, verbose=verbose)
    if is_lens:
        return (True, "Lens", "S2", lens_coeffs)
        
    # A couple more unusual names.
    if name == "T x S1":
        return (True, "Euclidean", "T", [])
    # KB x/~ S1 should be recognized here, but is not.

    # At this point, all remaining SFS should follow a standard naming convention.
    if not "SFS" == name[:3]:
        return (None, None, None, None)
    if "#" in name:
        return (None, None, None, None)
    if "U/" in name:
        return (None, None, None, None)
    
    
    found = None
    if "SFS [S2: " == name[:9]:
        found = True
        base = "S2"
        starting_char = 2
        trunc_name = name[9:-1]
        coeffs = trunc_name.split(" ")
        assert len(coeffs) > 2
        # This disallows lens spaces, which should have already been found.
    if "SFS [RP2/n2: " == name[:13]:
        found = True
        base = "RP2"
        starting_char = 1
        trunc_name = name[13:-1]
        coeffs = trunc_name.split(" ")
        assert len(coeffs) > 1
        # This disallows prism manifolds, which also have a SFS structure over S2.
        # Compare Hatcher, Theorem 2.3(d).
    if "SFS [T: " == name[:8]:
        found = True
        base = "T"
        starting_char = 0
        trunc_name = name[8:-1]
        coeffs = trunc_name.split(" ")
    if "SFS [KB/n2: " == name[:12]:
        found = True
        base = "KB"
        starting_char = 0
        trunc_name = name[12:-1]
        coeffs = trunc_name.split(" ")
        assert len(coeffs) > 0
        # This disallows KB x/~ S1, which also has a SFS structure over S2.
        # Compare Hatcher, Theorem 2.3(e).
    # We do not search for bases of higher complexity.
    
    if not found:
        return (None, None, None, None)


    # Massage the list coeffs to eliminate the fluff
    coeffs = [coeff.strip("(") for coeff in coeffs]
    coeffs = [coeff.strip(")") for coeff in coeffs]
    coeffs = [coeff.split(",") for coeff in coeffs]
    coeffs = [[int(p) for p in coeff] for coeff in coeffs]
    
    # Calculate the base Euler characteristic and Euler number of fibration.
    base_char = euler_char(starting_char, coeffs)
    base_num = euler_num(coeffs)
    verbose_print(verbose, 10, ["found SFS structure:", base, coeffs])
    verbose_print(verbose, 10, ["Euler characteristic", base_char, "Euler number", base_num])
    
    if base_char > 0:
        assert base_num != 0
        # if base_num == 0, we would have S2 x R geometry; those manifolds should have already been found.
        geom = "Elliptic"
    elif base_char == 0:
        if base_num == 0:
            geom = "Euclidean"
        else:
            geom = "Nil"
    elif base_char < 0:
        if base_num == 0:
            geom = "H2 x R"
        else:
            geom = "PSL2R"
            
    verbose_print(verbose, 10, ["Geometric type:", geom])
    return (found, geom, base, coeffs)


def is_sfs_over_disk_from_name(name, verbose=3):
    """
    Given a regina name, if it is a SFS over D^2 (and not a solid torus),
    return True and the coefficients. If not, or unsure, return (None, None).
    """

    verbose_print(verbose, 15, ["Entering is_sfs_over_disk_from_name"])

    if name == "SFS [M/n2: ]":
        # This manifold is Seifert fibered in two ways; the other is over a disk.
        return is_sfs_over_disk_from_name("SFS [D: (2,1) (2,1)]", verbose=verbose)    
    if not "SFS [D: (" == name[:9]:
        return (None, None)
    if "#" in name:
        return (None, None)
    if "U/" in name:
        # This handles pseudo-names with a "U/?" gluing
        return (None, None)
        
    name = name[8:-1] # regina names...
    coeffs = name.split(" ")
    assert len(coeffs) > 1
    coeffs = [coeff.strip("(") for coeff in coeffs]
    coeffs = [coeff.strip(")") for coeff in coeffs]
    coeffs = [coeff.split(",") for coeff in coeffs]
    coeffs = [[int(p) for p in coeff] for coeff in coeffs]
    verbose_print(verbose, 10, ["Found SFS structure over disk:", coeffs])
    return (True, coeffs)


def is_graph_pair_from_name(name):
    """
    Given a regina name, test to see if it is a graph manifold with exactly two pieces,
    each of which is SFS over a disk. If so, return True and the pieces.
    According to Regina documentation, a True answer guarantees that the manifold is not
    a SFS, because the gluing matrix does not send fibers to fibers.
    If not, or unsure, return (None, None).
    """
    
    if name == None:
        return(None, None)
    if "#" in name:
        return (None, None)
    if "U/m" not in name:
        # This also rules out graph loops of the form "SFS [A: (2,1)] / [ 0,-1 | -1,0 ]"
        return (None, None)

    tori = name.count("U/")
    # This counts all gluing tori, including "U/?" gluings in pseudo-name
    if tori != 1:
        return (None, None)
        
    A, B = name.split(", m =")[0].split(" U/m ")
    A_bool, A_coeffs = is_sfs_over_disk_from_name(A)
    B_bool, B_coeffs = is_sfs_over_disk_from_name(B)
    if A_bool and B_bool:
        return(True, [A, B])
        
    return (None, None)


def are_distinguished_lens_spaces(name0, name1, verbose = 3):
    '''
    Given two Regina names, checks whether the two manifolds are lens spaces.
    If yes, and the two are not homeomorphic, return True. If one is not
    a lens space, or they are homeomorphic, return False.
    This only tests for _un_oriented homeomorphism.
    '''
    
    verbose_print(verbose, 15, ["Entering are_distinguished_lens_spaces"])
    bool0, ints0 = is_lens_space_from_name(name0, verbose=verbose)
    bool1, ints1 = is_lens_space_from_name(name1, verbose=verbose)
    if not (bool0 and bool1):
        verbose_print(verbose, 12, [name0, name1, "at least one is not a lens space"])
        return False
    p0, q0 = ints0
    p1, q1 = ints1
    if p0 != p1:
        verbose_print(verbose, 4, [name0, name1, "lens spaces with different homology"])
        return True
    p = p0
    if ((q0 - q1) % p) == 0 or ((q0 + q1) % p) == 0 or ((q0 * q1) % p) == 1 or ((q0 * q1) % p) == -1 % p:
        verbose_print(verbose, 12, [name0, name1, "homeomorphic lens spaces"])
        return False
    verbose_print(verbose, 12, [name0, name1, "non-homeomorphic lens spaces"])
    return True


def are_distinguished_closed_sfs(name_0, name_1, verbose = 3):
    '''
    Given two Regina names, checks whether the two manifolds are SFS over S2,
    RP2, Torus, or Klein Bottle.
    If yes, and the two are not homeomorphic, return True. 
    Lens spaces are allowed, and are handled separately from others over S2.
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    This routine only tests for _un_oriented homeomorphism.
    '''

    verbose_print(verbose, 15, ["Entering are_distinguished_closed_sfs"])
    
    bool_0, geom_0, base_0, coeffs_0 = is_closed_sfs_from_name(name_0, verbose=verbose)
    bool_1, geom_1, base_1, coeffs_1 = is_closed_sfs_from_name(name_1, verbose=verbose)
    
    if not (bool_0 and bool_1):
        verbose_print(verbose, 12, [name_0, name_1, "at least one seems not to be a known closed SFS"])
        # so give up
        return False
        
    if base_0 != base_1:
        verbose_print(verbose, 12, [name_0, name_1, "different base orbifolds"])
        return True
        
    if geom_0 != geom_1:
        verbose_print(verbose, 12, [name_0, name_1, "different geometric types"])
        return True

    if geom_0 == "Lens" and geom_1 == "Lens":
        return are_distinguished_lens_spaces(name_0, name_1, verbose = verbose)
        
    # At this point, we know that both are SFS over the same base, and neither is a lens space.
   
    coeffs_0.sort()
    coeffs_1.sort()

    if len(coeffs_0) != len(coeffs_1):
        verbose_print(verbose, 12, [name_0, name_1, "different number of singular fibers"])
        return True

    cone_pts_0 = [p for (p, q) in coeffs_0]
    cone_pts_1 = [p for (p, q) in coeffs_1]
    # homework - check that regina sorts the coefficients.

    if cone_pts_0 != cone_pts_1: 
        verbose_print(verbose, 12, [name_0, name_1, "base orbifolds have different cone points"])
        return True

    eul_num_0 = euler_num(coeffs_0)
    eul_num_1 = euler_num(coeffs_1)
    
    if abs(eul_num_0) != abs(eul_num_1): 
        verbose_print(verbose, 12, [name_0, name_1, "Euler numbers are different"])
        return True

    # normed_coeffs_0 = [(p, q % p) for p, q in coeffs_0].sort()
    # normed_coeffs_1 = [(p, q % p) for p, q in coeffs_1].sort()
    # if normed_coeffs_0 != normed_coeffs_1: 
    #    verbose_print(verbose, 12, [name_0, name_1, "distinguished by singular fibers"])
    #    return True

    verbose_print(verbose, 12, [name_0, name_1, "could not distinguish."])
    return False


def are_distinguished_sfs_over_disk(name_0, name_1, verbose = 3):
    '''
    Given two Regina names, checks whether the two manifolds are SFS over disk.
    If yes, and the two are not homeomorphic, return True. 
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    This routine only tests for _un_oriented homeomorphism.
    '''

    bool_0, coeffs_0 = is_sfs_over_disk_from_name(name_0)
    bool_1, coeffs_1 = is_sfs_over_disk_from_name(name_1)
    coeffs_0.sort()
    coeffs_1.sort()

    if not (bool_0 and bool_1):
        verbose_print(verbose, 12, [name_0, name_1, "at least one seems not to be a sfs over disk"])
        # so give up
        return False 

    if len(coeffs_0) != len(coeffs_1):
        verbose_print(verbose, 12, [name_0, name_1, "different number of singular fibers"])
        return True

    cone_pts_0 = [p for (p, q) in coeffs_0]
    cone_pts_1 = [p for (p, q) in coeffs_1]
    # homework - check that regina sorts the coefficients.

    if cone_pts_0 != cone_pts_1: 
        verbose_print(verbose, 12, [name_0, name_1, "base orbifolds are different"])
        return True

    euler_num_0 = euler_num(coeffs_0, ModOne = True)
    euler_num_1 = euler_num(coeffs_1, ModOne = True) 
    if (euler_num_0 != euler_num_1) and (euler_num_0 + euler_num_1 != 1): 
        verbose_print(verbose, 12, [name_0, name_1, "euler numbers are different", euler_num_0, euler_num_1])
        return True

    # normed_coeffs_0 = [(p, q % p) for p, q in coeffs_0].sort()
    # normed_coeffs_1 = [(p, q % p) for p, q in coeffs_1].sort()
    # if normed_coeffs_0 != normed_coeffs_1: 
    #    verbose_print(verbose, 12, [name_0, name_1, "distinguished by singular fibers"])
    #    return True

    verbose_print(verbose, 12, [name_0, name_1, "could not distinguish."])
    return False


def are_distinguished_graph_pairs(name_0, name_1, verbose = 3):
    '''
    Given two Regina names, checks whether the two manifolds are graph pairs.
    If yes, and the two are not homeomorphic, return True. 
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    According to Regina documentation, a graph pair is guaranteed to not be a SFS, so the list
    of pieces is an invariant.
    This routine only tests for _un_oriented homeomorphism.
    '''

    bool_0, pieces_0 = is_graph_pair_from_name(name_0)
    bool_1, pieces_1 = is_graph_pair_from_name(name_1)

    if not (bool_0 and bool_1):
        verbose_print(verbose, 12, [name_0, name_1, "at least one seems not to be a graph pair"])
        # so give up
        return False 

    if are_distinguished_sfs_over_disk(pieces_0[0], pieces_1[0]) and are_distinguished_sfs_over_disk(pieces_0[0], pieces_1[1]):
        verbose_print(verbose, 12, [pieces_0[0], 'is not a piece of', name_1])
        return True

    if are_distinguished_sfs_over_disk(pieces_0[1], pieces_1[0]) and are_distinguished_sfs_over_disk(pieces_0[1], pieces_1[1]):
        verbose_print(verbose, 12, [pieces_0[1], 'is not a piece of', name_1])
        return True

    if are_distinguished_sfs_over_disk(pieces_1[0], pieces_0[0]) and are_distinguished_sfs_over_disk(pieces_1[0], pieces_0[1]):
        verbose_print(verbose, 12, [pieces_1[0], 'is not a piece of', name_0])
        return True

    if are_distinguished_sfs_over_disk(pieces_1[1], pieces_0[0]) and are_distinguished_sfs_over_disk(pieces_1[1], pieces_0[1]):
        verbose_print(verbose, 12, [pieces_1[1], 'is not a piece of', name_0])
        return True

    # We could also check the gluing matrices. We do not do this.

    verbose_print(verbose, 12, [name_0, name_1, "could not distinguish."])
    return False



def is_chiral_graph_mfd_from_name(name, verbose = 3):
    '''
    Given the Regina name of a graph manifold M assembled from Seifert fibered pieces,
    try a few tests to determine whether M is chiral. If chiral, return True.
    If the simple tests do not succeed, return None.
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    '''

    # Lens spaces
    # https://math.stackexchange.com/questions/2843946/which-lens-spaces-are-chiral
    # "Example 3.22 and Lemma 3.23 in Hempel give q^2 + 1 = 0 (mod p)
    # as a necessary and sufficient condition for L(p,q) to admit an
    # orientation-reversing homeomorphism."
    is_lens, ints = is_lens_space_from_name(name, verbose=verbose)
    if is_lens:
        p, q = ints
        if p == 0:
            return False
        else:
            return ((q**2 + 1) % p) != 0
    
    is_closed_sfs, _, _, coeffs = is_closed_sfs_from_name(name, verbose=verbose)
    if is_closed_sfs:
        # We know this is not a lens space, so Euler number is an invariant.
            
        eul = euler_num(coeffs)
        if eul != 0: 
            return True
        elif (len(coeffs) % 2 != 0) and ([2,1] not in coeffs) and ([2,-1] not in coeffs):
            # Any orientation-reversing bijection of the singular fibers would have to fix
            # a fiber of type [2,1] or [2,-1]. So, such a bijection cannot exist.
            return True
        else:
            # We could look for another fiberwise bijection that reverses signs.
            # But this is not currently implemented
            return None

    is_sfs_over_disk, coeffs = is_sfs_over_disk_from_name(name, verbose=verbose)
    if is_sfs_over_disk:
        eul = euler_num(coeffs, ModOne = True)
        if eul !=0 and eul != QQ((1, 2)):
            return True
        elif (len(coeffs) % 2 != 0) and ([2,1] not in coeffs) and ([2,-1] not in coeffs):
            # Any orientation-reversing bijection of the singular fibers would have to fix
            # a fiber of type [2,1] or [2,-1]. So, such a bijection cannot exist.
            return True
        else:
            # We could look for another fiberwise bijection that reverses signs.
            # But this is not currently implemented
            return None
        
    is_graph_pair, pieces = is_graph_pair_from_name(name)
    if is_graph_pair:
        name0, name1 = pieces
        distinct = are_distinguished_sfs_over_disk(name0, name1)
        if distinct:
            # Any self-homeo would have to send each piece to itself.
            verbose_print(verbose, 10, [name0, name1, 'are distinct pieces'])
            return (is_chiral_graph_mfd_from_name(name0) or is_chiral_graph_mfd_from_name(name1))
        else:
            _, coeffs0 = is_sfs_over_disk_from_name(name0)
            _, coeffs1 = is_sfs_over_disk_from_name(name1)
            eul0 = euler_num(coeffs0, ModOne = True)
            eul1 = euler_num(coeffs1, ModOne = True)
            sum_of_eul = eul0 + eul1
            verbose_print(verbose, 10, [name0, name1, 'homeomorphic pieces with Euler numbers summing to', sum_of_eul])
            # To have an orientation-reversing homeo from piece0 to piece1, their euler
            # numbers would have to be opposite (modulo 1).
            return (sum_of_eul != 0 and sum_of_eul != 1)

    if '#' in name:
        pieces = name.split(" # ")
        if len(pieces) == 2:
            name0, name1 = pieces
            if are_distinguished_closed_sfs(name0, name1, verbose = verbose):
                verbose_print(verbose, 10, [name0, name1, 'are distinct pieces'])
                return (is_chiral_graph_mfd_from_name(name0) or is_chiral_graph_mfd_from_name(name1))

    return None   

# Math

    
def product(nums):
    prod = 1
    for d in nums:
        prod = prod * d
    return prod


# Volume differences under filling


# we will need the following:

# eccen = 3.3957
# u(z) = (eccen/2) * (z**2 * (z**4 + 4*z**2 - 1)) / (z**2 + 1)**3
# v(z) = (eccen/4) * ( (-2*z**5 + z**4 - z**3 + 2*z**2 - z + 1)/(z**2+1)**2 + arctan(z) - arctan(1.0) )
# v(z) is the integral of u from z to 1.

def HK_vol_bound(L):
    """
    Given a normalised length L (which is at least 9.93), returns an
    upper bound on the change of volume when filling a slope of that
    normalised length. 
    Reference: Hodgson-Kerckhoff 'Shape of DS space', Thm 5.12.
    Reference: our Theorem 2.7, which is a secant line approx to the above.
    """
    assert L >= 9.93
    z = 1 - (14.77)/L**2
    return RIF(3.3957/4.0) * ( (-2*z**5 + z**4 - z**3 + 2*z**2 - z + 1)/(z**2 + 1)**2 + arctan(z) - arctan(RIF(1)) )

# Recall that HK_vol_bound is decreasing (for L > 5.6 or so).  So we may
# use bisection to invert. This appears to be fast enough.

def HK_vol_bound_inv(diff_vol, digits = 2):
    """
    Given a _difference_ in volumes, diff_vol, returns an interval
    about a normalised length, said length ensuring that the true
    difference (drilled minus filled) is at most diff_vol.
    """
    
    L = RIF(9.95)  # the lowest length we can return
    
    if HK_vol_bound(L) <= diff_vol:
        return L
    while HK_vol_bound(L) > diff_vol:
        L = 2.0*L
    L_up = L
    L_down = L/2.0
    while L_up - L_down > 10.0**(-digits):
        L_mid = (L_up + L_down)/2.0
        if HK_vol_bound(L_mid) > diff_vol:
            L_down = L_mid
        else:
            L_up = L_mid
    return L_up
            

# Cusped manifolds with H_1(M) = Z can be ruled out via Boyer-Lines
# criterion on Casson invariant (second deriv of Alexander polynomial)

def Casson_invt(M, verbose):
    P = M.alexander_polynomial()
    verbose_print(verbose, 10, [P, 'Alexander polynomial'])
    deg = P.degree()/2
    Rin = P.parent()  # the polynomial ring where P lives
    # Assume that P is a polynomial in one variable
    # normalize the polynomial so that positive and negative powers match and
    # so that it evaluates to 1 at 1
    Q = P/(Rin.gen()**deg * P(1))  
    verbose_print(verbose, 10, [Q, 'Normalized Alexander polynomial'])
    assert Q(1) == 1
    A = Q.derivative().derivative()
    verbose_print(verbose, 10, [A, 'second derivative'])
    return A(1)/2

# Homology


def order_of_torsion(M):
    """
    Given a snappy manifold return the order of the torsion subgroup
    of H_1(M).
    """
    H = M.homology()
    elem_divs = H.elementary_divisors()
    torsion_divs = [d for d in elem_divs if d != 0]
    return product(torsion_divs)


def check_cover_homology_fixed_deg(M, N, deg, verbose=5):
    """
    Given a pair of snappy manifolds, M and N, and a degree deg,
    build all covers of M and N of degree deg. Compute homology groups of each.
    Check whether the sets match.
    """

    M_homologies = set( str(K.homology()) for K in M.covers(deg))
    N_homologies = set( str(K.homology()) for K in N.covers(deg))

    verbose_print(verbose, 12, [M, 'degree', deg, M_homologies])
    verbose_print(verbose, 12, [N, 'degree', deg, N_homologies])

    if M_homologies != N_homologies:
        verbose_print(verbose, 6, [M, N, 'distinguished by cover homology at degree', deg])
        return True
    else:
        return False


def is_distinguished_by_covers(M, s, N, t, tries, verbose):
    """
    Given snappy manifolds M and N, and a pair of slopes s and t, builds
    M(s) and N(t), computes a collection of covers of each, counts
    them, and returns True if the "spectrum" distinguishes.  If this
    fails, returns False.
    """
    
    verbose_print(verbose, 12, [M, s, N, t, "entering is_distinguished_by_covers"])
    Ms = M.copy()
    Nt = N.copy()
    Ms.dehn_fill(s)
    Nt.dehn_fill(t)

    Ms_covers = [len(Ms.covers(i)) for i in range(2, 6)]
    Nt_covers = [len(Nt.covers(i)) for i in range(2, 6)]

    if Ms_covers != Nt_covers:
        verbose_print(verbose, 6, [M, s, N, t, 'cover spectrum distinguishes'])
        return True

    return False

    
def is_distinguished_by_cover_homology(M, s, N, t, tries, verbose):
    """
    Given a snappy manifold M and a pair of slopes s and t, builds
    M(s) and M(t), computes a collection of covers of each, computes
    the homology groups of those covers and finally returns True if that
    invariant distinguishes.  If this fails, returns False.
    """

    verbose_print(verbose, 12, [M, s, N, t, "entering is_distinguished_by_cover_homology"])

    Ms = M.copy()
    Nt = N.copy()
    Ms.dehn_fill(s)
    Nt.dehn_fill(t)

    if Ms.homology() != Nt.homology():
        # This was not supposed to happen, but does because half-lives-half-dies only works over Q. 
        verbose_print(verbose, 5, [Ms, Ms.homology(), ',', Nt, Nt.homology(), 'distinguished by homology groups'])
        return True

    order = order_of_torsion(Ms)
    if order != 1:
        factors = list(factor(order))
        factors = [f[0] for f in factors] # strip the powers
        factors.sort()   
        p = factors[0] # smallest prime
        # first, try covers of degree exactly p
        if p < tries:
            distinct = check_cover_homology_fixed_deg(Ms, Nt, p, verbose)
            if distinct:
                return True

    # Now, try all covers of small degree
    cap = min(tries, 8) # do not bother with covers of degree more than 7
    for deg in range(1, cap):
        distinct = check_cover_homology_fixed_deg(Ms, Nt, deg, verbose)
        if distinct:
            return True
    return False


# hyperbolic invariants


def is_amphichiral(M, tries=8, verbose=3):
    """
    Given an orientable hyperbolic cusped Snappy three-manifold,
    decides if it has an orientation reversing isometry.
    
    Returns a Boolean and (if amphichiral) an orientation-reversing
    change of basis matrix for the cusp.
    """
    verbose_print(verbose, 12, [M, 'entering is_amphichiral'])

    assert M.is_orientable()
    assert M.num_cusps() > 0

    M = dunfield.find_positive_triangulation(M, tries=tries, verbose=verbose)

    G = M.symmetry_group()
    amph = G.is_amphicheiral()
    
    if not amph:
        return (False, None)
    
    cob = None
    for iso in G.isometries(): 
         image = iso.cusp_images()[0] # Where the 0-th cusp goes
         cob = iso.cusp_maps()[0]     # change of basis matrix
         if image == 0 and det(cob) == -1:
             break

    return (amph, cob)


### This function is not rigorous - also it is never called.  So we
### should delete this...
def is_exceptional_due_to_volume(M, verbose):
    verbose_print(verbose, 12, [M, 'entering is_exceptional_due_to_volume'])
    if M.volume() < 0.9:
        verbose_print(verbose, 6, [M, 'has volume too small...'])
        verbose_print(verbose, 6, [M.fundamental_group()])
        return True


def fetch_exceptional_data(M, s, exceptions_table, field, tries = 3, verbose = 2):
    '''
    Given a manifold M (assumed to be one-cusped), we wish to construct
    and update the exceptions_table.  This is a database where the
    keys are slopes (here s).  The fields are useful data about
    exceptional fillings that we don't want to compute twice.  Remark:
    If we fail to compute an invariant, we don't install anything in
    the table and just return None.
    '''
    # convention - no empty fields - aka no placeholders. 

    verbose_print(verbose, 12, [M, s, "entering exceptions table", field])
    
    allowed_fields = ["fund_gp", "name", "atoroidal_sfs", "reducible", "toroidal"]
    # The field "lens" used to be allowed, but it is no more.
    assert field in allowed_fields
    
    if not s in exceptions_table:
        exceptions_table[s] = {}

    if field in exceptions_table[s]:
        verbose_print(verbose, 10, [M, s, field, 'found in table'])
        return exceptions_table[s][field]
    
    # We did not find the field, so we have to install and return it.

    N = M.copy()
    N.dehn_fill(s)
    
    if field == "fund_gp":
        out = fundamental.is_exceptional_due_to_fundamental_group(N, tries, verbose)
        is_except, _ = out
        if is_except:
            exceptions_table[s]["fund_gp"] = out
        return out
    
    if field == "name":
        try:
            name = dunfield.regina_name(N)
        except:
            print(N)
            raise
        if name != None:
            exceptions_table[s]["name"] = name
            verbose_print(verbose, 10, [N, name, 'added to table'])
            return name
        else:
            # try to see if N is a toroidal mixed manifold
            is_tor, pieces = fetch_exceptional_data(M, s, exceptions_table, "toroidal", tries, verbose)
            if is_tor:
                # Convert the list of JSJ pieces into a pseudo-name
                piece_names = [p[1] for p in pieces]
                name = ' U/? '.join(sorted(piece_names))
                exceptions_table[s]["name"] = name
                verbose_print(verbose, 10, [N, name, 'pseudo-name added to table'])
                return name
            else:
                verbose_print(verbose, -1, [N, "could not compute name"])
                return None
    
    if field == "atoroidal_sfs":
        name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
        if name == None:
            return (None, None)

        out = is_closed_sfs_from_name(name)
        is_sfs, geom, base, coeffs = out
        if is_sfs and geom in ["Lens", "Elliptic", "S2 x R"]:
            exceptions_table[s]["atoroidal_sfs"] = out
            verbose_print(verbose, 10, [N, name, 'Atoroidal sfs coeffs added to table'])
            return out
        elif is_sfs and base == "S2" and (len(coeffs) <= 3):
            exceptions_table[s]["atoroidal_sfs"] = out
            verbose_print(verbose, 10, [N, name, 'Atoroidal sfs coeffs added to table'])
            return out        
        else:
            verbose_print(verbose, 10, [N, s, name, "Not recognized as atoroidal SFS"])
            return (None, geom, base, coeffs)
        
    if field == "reducible":
        out = geom_tests.is_reducible_wrapper(N, tries, verbose)
        exceptions_table[s]["reducible"] = out
        verbose_print(verbose, 10, [N, out, 'reducibility'])
        return out
        
    if field == "toroidal":
        out = geom_tests.torus_decomp_wrapper(N, tries, verbose)
        exceptions_table[s]["toroidal"] = out
        verbose_print(verbose, 10, [N, out, 'toroidality'])
        return out
        
        
def fetch_volume(M, s, volumes_table, tries, verbose):
    '''
    Given a manifold M (assumed to be one-cusped and equipped with a
    good triangulation) and a slope s (assumed to be hyperbolic),
    fetch the volume. This means: pull the volume from the table
    if it is there; else, try to compute it, and then store in the table.
    Return the volume either way.
    '''
    verbose_print(verbose, 12, [M, s, "entering fetch_volume"])

    if s in volumes_table:
        verbose_print(verbose, 10, [M, s, 'volume found in table'])
        return volumes_table[s]
    else:
        verbose_print(verbose, 10, [M, s, 'trying to compute volume'])
                
        assert M.solution_type() == 'all tetrahedra positively oriented'

        N = M.copy() 
        N.dehn_fill(s)

        # will need to wrap this in a try/except. 
        is_hyp, vol = dunfield.is_hyperbolic_with_volume(N, tries = tries, verbose = verbose)
        if not is_hyp:
            verbose_print(verbose, -1, [N, 'positive triangulation fail - putting untrusted volume in the table'])
            R = RealIntervalField(10) # downgrade the precision!
            volumes_table[s] = R(N.volume())
        else: 
            volumes_table[s] = vol

    return volumes_table[s]
        


def is_hyperbolic_filling(M, s, mer_hol, long_hol, exceptions_table, tries, verbose):
    '''
    Given a one-cusped manifold M (assumed hyperbolic) and a slope s,
    try to determine if M(s) is hyperbolic or exceptional.  Returns
    True or False respectively, and returns None if we failed.
    '''
    verbose_print(verbose, 12, [M, s, 'entering is_hyperbolic_filling'])
    p, q = s
    # We don't recompute cusp_invariants because it is slow
    # m, l, _ = cusp_invariants(C)
    if abs(p*mer_hol + q*long_hol) > 6: # six-theorem
        verbose_print(verbose, 10, [M, s, 'has length', abs(p*mer_hol + q*long_hol), 'hence the filling is hyperbolic by 6-theorem'])
        return True            

    N = M.copy()
    N.dehn_fill(s)

    for i in range(tries):

        # I swapped the order, to place fund_gp before is_hyp.  This
        # is because (I hope!) the fundamental group routines will
        # hopefully weed out the Milley manifolds (eg s297(1,-1),
        # s713(1,-1), v1621(1,1)) causing (very rare and also random)
        # crashes in is_hyp.  This may also give us a speed-up.

        for j in range(i + 1):
            N.randomize()  # Note: the randomized triangulation will stay with us until the next i
            is_except, _ = fetch_exceptional_data(M, s, exceptions_table, "fund_gp", tries, verbose)
            if is_except:
                return False
            
        for j in range(1): # this is not a typo.  :P
            if dunfield.is_hyperbolic(N, 2*i + 1, verbose): # because Nathan randomises for us.
                # at this moment we trust the volume so put it in the table?
                return True
            
        if i == 0: # this is trustworthy and expensive.
            is_tor, _ = fetch_exceptional_data(M, s, exceptions_table, "toroidal", tries, verbose)
            if is_tor: 
                return False
            
    # ok, nothing "easy" worked

    name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
    if name == None:
        # We have failed.  Very sad.
        return None
    elif name[:3] == 'SFS': # We trust regina_name.
        return False
    elif "#" in name:
        return False

    # We have failed.  Very sad.
    verbose_print(verbose, -1, [name, "Is_hyperbolic_filling failed. Think about how to handle it!"])
    return None


    
# dealing with a pair of slopes



def is_distinguished_non_hyp(L, s, t, tries, verbose):
    '''
    Given a manifold L and two slopes (where we think that both
    fillings are non-hyperbolic), try to prove that L(s) is not
    homeomorphic to L(t). Invariants that we check include (in order):
    1) Homology
    2) Irreducibility (via Regina)
    3) Toroidality (via Regina)
    4) Number of covers of small degree
    '''
    verbose_print(verbose, 12, [L, s, t, 'entering is_distinguished_non_hyp'])
    M = L.copy()
    N = L.copy()
    
    M.dehn_fill(s)
    N.dehn_fill(t)

    # finish or delete
    
    return None        


# finding common fillings of M and N



def find_common_fillings(M, N, check_chiral=False, tries=8, verbose=4):
    '''
    Given one-cusped manifolds M and N, we search for common Dehn fillings,
    that is, pairs of slopes s,t such that M(s) might be homeomorphic to N(t).
    
    Return a list of tuples - (M, s, N, t, 'reason') where M(s) and N(t)
    are possibly the same manifold. The output should contain the list of
    potential pairs, but might have some fluff (non-distinguished pairs).
    
    If check_chiral==False, then we only check for orientation-preserving
    homeos.

    If check_chiral==True, then we check for both orientation-preserving
    and orientation-reversing homeos.
    
    This routine is designed for the situation when M != N. If M == N, use check_cosmetic instead.
    '''

    verbose_print(verbose, 12, [M, N, "entering find_common_fillings"])
    
    # Let's be liberal in what we accept
    if type(M) is snappy.Manifold:
        M_name = M.name()
    elif type(M) is str:
        M_name = M
        M = snappy.Manifold(M_name)
    if type(N) is snappy.Manifold:
        N_name = N.name()
    elif type(N) is str:
        N_name = N
        N = snappy.Manifold(N_name)
    
    # but not too liberal!

    if not M.num_cusps() == 1:
        return [(M_name, None, None, None, 'wrong number of cusps')]
    if not N.num_cusps() == 1:
        return [(N_name, None, None, None, 'wrong number of cusps')]

    # Install good hyperbolic metrics on M or N. Give up if we cannot find such a metric.
        
    mfd, reason = geom_tests.sanity_check_cusped(M, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure, so give up.
        return [(M_name, None, None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        M = mfd
    mfd, reason = geom_tests.sanity_check_cusped(N, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure, so give up.
        return [(N_name, None, None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        N = mfd

    if M.is_isometric_to(N):
        # All their Dehn fillings will coincide
        verbose_print(verbose, 3, [M_name, N_name, 'are isometric'])    
        return [(M_name, None, N_name, None, 'isometric parent manifolds')]

    # Step zero - Find the volume and systole of both M and N. 

    M_volumes_table = {}  # Lookup table of volumes of hyperbolic fillings
    M_vol = fetch_volume(M, (0,0), M_volumes_table, tries, verbose)
    M_exceptions_table = {}  # Lookup table of information about non-hyperbolic fillings
        
    M_sys = geom_tests.systole_with_tries(M, tries=tries, verbose=verbose)
    verbose_print(verbose, 3, [M_name, 'systole is at least', M_sys])
    if M_sys == None:
        return [(M_name, None, None, None, 'systole fail')]
    
    M_norm_len_cutoff = max(9.97, sqrt((2*pi/M_sys) + 56.0).n(200)) 
    verbose_print(verbose, 4, [M_name, 'norm_len_cutoff', M_norm_len_cutoff])

    N_volumes_table = {}  # Lookup table of volumes of hyperbolic fillings
    N_vol = fetch_volume(N, (0,0), N_volumes_table, tries, verbose)
    N_exceptions_table = {}  # Lookup table of information about non-hyperbolic fillings
        
    N_sys = geom_tests.systole_with_tries(N, tries=tries, verbose=verbose)
    verbose_print(verbose, 3, [N_name, 'systole is at least', N_sys])
    if N_sys == None:
        return [(N_name, None, None, None, 'systole fail')]
    
    N_norm_len_cutoff = max(9.97, sqrt((2*pi/M_sys) + 56.0).n(200)) 
    verbose_print(verbose, 4, [N_name, 'norm_len_cutoff', N_norm_len_cutoff])
        
    
    # Step one - fix the framing of both M and N and gather the invariants that can
    # be found rigorously.

    M.set_peripheral_curves('shortest')
    M_mer_hol, M_long_hol, M_norm_fac = geom_tests.cusp_invariants(M)
    M_l_hom = geom_tests.preferred_rep(M.homological_longitude())
    M_m_hom = geom_tests.shortest_complement(M_l_hom, M_mer_hol, M_long_hol)
    
    verbose_print(verbose, 4, [M_name, 'cusp_stuff', 'merid', M_mer_hol, 'long', M_long_hol])
    verbose_print(verbose, 5, ['cusp_stuff', 'norm_fac', M_norm_fac, 'homolog. long.', M_l_hom, 'homolog. merid.', M_m_hom])
    
    N.set_peripheral_curves('shortest')
    N_mer_hol, N_long_hol, N_norm_fac = geom_tests.cusp_invariants(N)
    N_l_hom = geom_tests.preferred_rep(N.homological_longitude())
    N_m_hom = geom_tests.shortest_complement(N_l_hom, N_mer_hol, N_long_hol)
    
    verbose_print(verbose, 4, [N_name, 'cusp_stuff', 'merid', N_mer_hol, 'long', N_long_hol])
    verbose_print(verbose, 5, ['cusp_stuff', 'norm_fac', N_norm_fac, 'homolog. long.', N_l_hom, 'homolog. merid.', N_m_hom])

    # TO HERE 2022.12.06 - off-ramp for now
    return None


    # Step two - get the short slopes. Split them by homology
           
    M_short_slopes = geom_tests.find_short_slopes(M, M_norm_len_cutoff, normalized=True, verbose=verbose)                    
    verbose_print(verbose, 3, [M_name, len(short_slopes), 'short slopes found'])
    verbose_print(verbose, 5, M_short_slopes)

    N_short_slopes = geom_tests.find_short_slopes(N, N_norm_len_cutoff, normalized=True, verbose=verbose)                    
    verbose_print(verbose, 3, [M_name, len(short_slopes), 'short slopes found'])
    verbose_print(verbose, 5, M_short_slopes)
    

    slopes_by_homology = {}
    for s in short_slopes:
        p = abs(geom_tests.alg_int(s, l_hom))
        if p == 0:
            verbose_print(verbose, 4, [name, 'removing homological longitude'])
            continue # the homological longitude is unique, so cannot be cosmetic
        N = M.copy()
        N.dehn_fill(s)
        hom_gp = str(N.homology())
        
        # This test fails and also is unnecessary.  See Lem:TorsionInHalfLivesHalfDies
        # assert ( ( order_of_torsion(N) / order_of_torsion(M) ) - p ) < 0.01, str(M.name()) + ' ' + str(s)
        
        hom_hash = (p, hom_gp)  # Note that p is redunant by Lemma~\ref{Lem:HomologyTorsion}
        add_to_dict_of_sets(slopes_by_homology, hom_hash, s)

    verbose_print(verbose, 0, [name, 'slopes_by_homology', slopes_by_homology]) # Normally, the cutoff should be 5.
        
    # Step three - split slopes_by_homology into slopes_hyp, slopes_non_hyp, slopes_bad

    slopes_hyp = {}
    slopes_non_hyp = {}
    slopes_bad = {}
    for hom_hash in slopes_by_homology:
        for s in slopes_by_homology[hom_hash]:
            hyp_type = is_hyperbolic_filling(M, s, mer_hol, long_hol, exceptions_table, tries, verbose)
            if hyp_type == True:
                add_to_dict_of_sets(slopes_hyp, hom_hash, s)
            if hyp_type == False:
                add_to_dict_of_sets(slopes_non_hyp, hom_hash, s)
            if hyp_type == None: 
                add_to_dict_of_sets(slopes_bad, hom_hash, s)

    num_hyp_slopes = sum(len(slopes_hyp[hash]) for hash in slopes_hyp)
    num_non_hyp_slopes = sum(len(slopes_non_hyp[hash]) for hash in slopes_non_hyp)
    num_bad_slopes = sum(len(slopes_bad[hash]) for hash in slopes_bad)
    verbose_print(verbose, 3, [name, num_hyp_slopes, 'hyperbolic', num_non_hyp_slopes, 'exceptional', num_bad_slopes, 'bad'])
    verbose_print(verbose, 4, [name, len(slopes_hyp), 'homology buckets of hyperbolic slopes'])
    verbose_print(verbose, 5, [name, 'hyp slopes', slopes_hyp])
    verbose_print(verbose, 5, [name, 'non-hyp slopes', slopes_non_hyp])
    if len(slopes_bad) > 0:
        verbose_print(verbose, 0, [name, 'bad slopes', slopes_bad])


    # Step four - check for (non-hyperbolic) cosmetic pairs in slopes_non_hyp[hom_hash].
    # Note that slopes_bad automatically gets recorded and reported.

    bad_uns = []
    for hom_hash in slopes_bad:
        for s in slopes_bad[hom_hash]:
            reason = (name, hom_hash, s, 'Could not verify hyperbolicity')
            verbose_print(verbose, 2, [reason])
            bad_uns.append(reason)

    for hom_hash in slopes_non_hyp:
        for s in slopes_non_hyp[hom_hash]:
            for t in slopes_non_hyp[hom_hash]:
                if t < s:
                    # We will have checked the pair (t, s) separately.
                    continue 
                if geom_tests.alg_int(s, t) == 0:
                    # Parallel slopes cannot be cosmetic.
                    continue

                s_name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
                t_name = fetch_exceptional_data(M, t, exceptions_table, "name", tries, verbose)

                reason = (name, s, t, s_name, t_name)
                verbose_print(verbose, 10, ["comparing", s_name, "to", t_name])

                # Rapid tests that require only s_name and t_name     

                if "#" in s_name or "#" in t_name:
                    if abs(geom_tests.alg_int(s,t)) > 1:
                        # Gordon and Luecke proved distance between reducible fillings must be 1.
                        verbose_print(verbose, 2, [s_name, t_name, "distinguished by Gordon-Luecke theorem on distance between reducible fillings"])
                        continue
                s_lens, _ = is_lens_space_from_name(s_name, verbose)
                t_lens, _ = is_lens_space_from_name(t_name, verbose)
                if s_name == "S2 x S1" or s_lens or t_name == "S2 x S1" or t_lens:
                    if abs(geom_tests.alg_int(s,t)) > 1:
                        # Cyclic surgery theorem
                        verbose_print(verbose, 2, [s_name, t_name, "distinguished by cyclic surgery theorem"])
                        continue
                
                if are_distinguished_closed_sfs(s_name, t_name, verbose):
                    continue
                if are_distinguished_graph_pairs(s_name, t_name, verbose):
                    continue
                 
                s_ator_sfs, s_geom, _, _ = fetch_exceptional_data(M, s, exceptions_table, "atoroidal_sfs", tries, verbose)
                t_ator_sfs, t_geom, _, _ = fetch_exceptional_data(M, t, exceptions_table, "atoroidal_sfs", tries, verbose)

                # Less rapid tests, which require the name of one manifold and normal surface theory on the other.

                if s_ator_sfs:
                    t_red, _ = fetch_exceptional_data(M, t, exceptions_table, "reducible", tries, verbose)
                    if s_geom != "S2 x R" and t_red:
                        # M(s) is irreducible but M(t) is reducible
                        continue
                    t_tor, _ = fetch_exceptional_data(M, t, exceptions_table, "toroidal", tries, verbose)
                    if t_tor:
                        # M(s) is atoroidal but M(t) is toroidal
                        continue                    
                if t_ator_sfs:
                    s_red, _ = fetch_exceptional_data(M, s, exceptions_table, "reducible", tries, verbose)
                    if t_geom != "S2 x R" and s_red:
                        # M(t) is irreducible but M(s) is reducible
                        continue                    
                    s_tor, _ = fetch_exceptional_data(M, s, exceptions_table, "toroidal", tries, verbose)
                    if s_tor:
                        # M(t) is atoroidal but M(s) is toroidal
                        continue
                
                # At this point, both manifolds should be reducible, or both toroidal (or we have failed to identify a SFS).

                # Tests that search for covers are pretty slow, but effective.                    
                if is_distinguished_by_covers(M, s, M, t, tries, verbose):
                    continue

                if is_distinguished_by_cover_homology(M, s, M, t, tries, verbose):
                    continue

                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)



    # Step five - Compute the max of the volumes in
    # slopes_hyp[hom_hash] and use this to compute the larger set of
    # "comparison slopes".

    max_volumes = {}
    for hom_hash in slopes_hyp:
        max_volumes[hom_hash] = max(fetch_volume(M, s, volumes_table, tries, verbose) for s in slopes_hyp[hom_hash])

    verbose_print(verbose, 5, [name, 'max volumes by homology', max_volumes])

    # len_m_hom = abs(m_hom[0]*mer_hol + m_hom[1]*long_hol)
    len_l_hom = abs(l_hom[0]*mer_hol + l_hom[1]*long_hol)
    slopes_low_volume = {}
    for hom_hash in slopes_hyp:
        verbose_print(verbose, 25, ['slopes hyp', slopes_hyp[hom_hash]])
        # M_vol is the volume of the unfilled manifold M
        l_max = HK_vol_bound_inv(M_vol - max_volumes[hom_hash]) * norm_fac # length on cusp
        if verbose > 25:
            print('hom_hash, max_vol[hom_hash]', hom_hash, max_volumes[hom_hash])
            print('l_max', l_max, 'l_max_normalized', HK_vol_bound_inv(M_vol - max_volumes[hom_hash]))
            print('normalized length endpoints', (l_max/norm_fac).endpoints(),)
            print('norm_fac', norm_fac.endpoints())
            print('len_l_hom', len_l_hom)

        p, hom_gp = hom_hash
        point = (p*m_hom[0], p*m_hom[1])
        middle = geom_tests.a_shortest_lattice_point_on_line(point, l_hom, mer_hol, long_hol)
        lower = int( (-l_max / len_l_hom).floor().lower() )
        upper = int( (l_max / len_l_hom).ceil().upper() )
        verbose_print(verbose, 25, ['lower, upper', lower, upper])
        for k in range(lower, upper + 1):
            verbose_print(verbose, 25, ['k', k])
            # move along the line 
            a = middle[0] + k * l_hom[0] 
            b = middle[1] + k * l_hom[1]
            t = geom_tests.preferred_rep((a, b))
            a, b = t
            verbose_print(verbose, 25, ['t', t])
            if gcd(a, b) > 1:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because gcd'])
                continue
            N = M.copy()
            N.dehn_fill(t)
            hom_gp_t = str(N.homology())
            if hom_gp_t != hom_gp:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because wrong homology'])
                continue
            # now we now that (p, hom_gp_t) are correct, so we can use the dictionaries we built
            if hom_hash in slopes_non_hyp and t in slopes_non_hyp[hom_hash]:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because non-hyp'])
                continue
            if hom_hash in slopes_bad and t in slopes_bad[hom_hash]:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because bad'])
                continue
            # Thus t is a hyperbolic filling, so 
            # First, check length
            verbose_print(verbose, 25, ['lengths', abs(a*mer_hol + b*long_hol), l_max])
            if abs(a*mer_hol + b*long_hol) <= l_max:
                # Then, check the volume
                t_vol = fetch_volume(M, t, volumes_table, tries, verbose)
                verbose_print(verbose, 25, ['t_vol', t_vol])
                verbose_print(verbose, 25, ['max_vol[hom_hash]', max_volumes[hom_hash]])
                if not t_vol > max_volumes[hom_hash]:   # We need the 'not' because we are comparing intervals
                    add_to_dict_of_sets(slopes_low_volume, hom_hash, t)
                    verbose_print(verbose, 25, ['added to slopes_low_volume'])
        # Sanity check: slopes_hyp[hom_hash] should be a subset of slopes_low_volume[hom_hash]
        for t in slopes_hyp[hom_hash]:
            assert t in slopes_low_volume[hom_hash]

    num_low_volume = sum(len(slopes_low_volume[hash]) for hash in slopes_low_volume)
    verbose_print(verbose, 3, [name, num_low_volume, 'low volume slopes found'])
    verbose_print(verbose, 5, [name, '(somewhat-)low volume slopes', slopes_low_volume])


    # Step six - check for hyperbolic cosmetic pairs.
    # That is: for all p, slopes s in slopes_hyp[hom_hash], and slopes t in
    # slopes_low_volume[hom_hash] (with s \neq t) show that M(s) is not
    # orientation-preservingly homeomorphic to M(t).  Collect
    # counterexamples and difficult cases to be returned to calling
    # function.

    for hom_hash in slopes_hyp:
        for s in slopes_hyp[hom_hash]:
            for t in slopes_low_volume[hom_hash]:
                if t in slopes_hyp[hom_hash] and t < s:
                    # since slopes_hyp[hom_hash] \subset
                    # slopes_low_volume[hom_hash] we have (or will)
                    # checked the pair (t, s) so skip!
                    continue 
                if geom_tests.alg_int(s,t) == 0:
                    continue
                s_vol = fetch_volume(M, s, volumes_table, tries, verbose)
                t_vol = fetch_volume(M, t, volumes_table, tries, verbose)
                verbose_print(verbose, 12, [M, s, t, s_vol, t_vol, 'volumes'])
                if s_vol > t_vol or t_vol > s_vol:
                    verbose_print(verbose, 6, [M, s, t, 'verified volume distinguishes'])
                    continue
                looks_distinct, rigorous = False, False
                if not check_chiral:
                    # Try to distinguish by oriented hyperbolic invariants
                    looks_distinct, rigorous = geom_tests.is_distinguished_by_hyp_invars(M, s, t, tries, verbose)
                    if looks_distinct and rigorous:
                        continue
                    
                if is_distinguished_by_covers(M, s, M, t, tries, verbose):
                    continue
                if is_distinguished_by_cover_homology(M, s, M, t, tries, verbose):
                    continue
                    
                if looks_distinct and not rigorous:
                    reason = (name, s, t, 'distinguished by non-rigorous length spectrum')
                if not looks_distinct:
                    reason = (name, s, t, 'Not distinguished by hyperbolic invariants or covers')
                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)

    verbose_print(verbose, 1, [name, 'non-distinguished pairs', bad_uns])
    
    return bad_uns


def check_cosmetic(M, use_BoyerLines=True, check_chiral=False, tries=8, verbose=4):
    '''
    Given a one-cusped manifold M we equip it with a shortest framing
    and then return a list of tuples - (name, s, t, 'reason') where s
    and t are possibly a cosmetic pair.
    
    If use_BoyerLines==True, then we apply the Boyer-Lines theorem:
    the Casson invariant obstructs purely cosmetic surgeries.
    
    If check_chiral==False, then we only check for purely cosmetic 
    surgeries. 

    If check_chiral==True, then we check for chirally cosmetic surgeries
    as well as purely cosmetic ones. 
    '''

    verbose_print(verbose, 12, [M, "entering check_cosmetic"])
    
    # Let's be liberal in what we accept
    if type(M) is snappy.Manifold:
        name = M.name()
    if type(M) is str:
        name = M
        M = snappy.Manifold(name)

    # but not too liberal!

    if not M.num_cusps() == 1:
        return [(name, None, None, 'wrong number of cusps')]
        
    # If H_1(M) = Z, we can apply the Boyer-Lines criterion to rule out cosmetic surgeries

    if use_BoyerLines and not check_chiral:
        h = M.homology()
        if h.betti_number() == 1 and h.rank() == 1:
            # M is the complement of a knot in an integer homology sphere
            if Casson_invt(M, verbose) != 0:
                # The second derivative of the Alexander polynomial at 1 is nonzero,
                # so M has no cosmetic surgeries by Boyer-Lines
                verbose_print(verbose, 2, [M, 'has no cosmetic surgeries by Boyer-Lines'])
                return []

    # From now on, we need geometry. Install a good hyperbolic metric,
    # or give up if we cannot find one.
    
    mfd, reason = geom_tests.sanity_check_cusped(M, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure, so give up.
        return [(name, None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        M = mfd

    # Step one: identify exceptional fillings
    
    M.set_peripheral_curves('shortest')
    # C = M.cusp_neighborhood()
    # C.set_displacement(C.stopping_displacement())
    mer_hol, long_hol, norm_fac = geom_tests.cusp_invariants(M)
    l_hom = geom_tests.preferred_rep(M.homological_longitude())
    m_hom = geom_tests.shortest_complement(l_hom, mer_hol, long_hol)
    
    verbose_print(verbose, 4, [name, 'cusp_stuff', 'merid', mer_hol, 'long', long_hol])
    verbose_print(verbose, 5, ['cusp_stuff', 'norm_fac', norm_fac, 'homolog. long.', l_hom, 'homolog. merid.', m_hom])

    six_theorem_length = 6.01 # All exceptionals shorter than this
    exceptions_table = {}  # Lookup table of information about non-hyperbolic fillings
    slopes_hyp = {}
    slopes_non_hyp = {}
    slopes_bad = {}

    six_short_slopes = geom_tests.find_short_slopes(M, six_theorem_length, normalized=False, verbose=verbose)
    for s in six_short_slopes:
        p = abs(geom_tests.alg_int(s, l_hom))
        if p == 0:
            verbose_print(verbose, 4, [name, 'removing homological longitude'])
            continue # the homological longitude is unique, so cannot be cosmetic
        N = M.copy()
        N.dehn_fill(s)
        hom_gp = str(N.homology())
                
        hom_hash = (p, hom_gp)  # Note that p is redunant by Lemma~\ref{Lem:HomologyTorsion}
        hyp_type = is_hyperbolic_filling(M, s, mer_hol, long_hol, exceptions_table, tries, verbose)
        if hyp_type == True:
            add_to_dict_of_sets(slopes_hyp, hom_hash, s)
        if hyp_type == False:
            add_to_dict_of_sets(slopes_non_hyp, hom_hash, s)
        if hyp_type == None: 
            add_to_dict_of_sets(slopes_bad, hom_hash, s)

    
    # Step two: check for (non-hyperbolic) cosmetic pairs in slopes_non_hyp.
    # Note that slopes_bad automatically gets recorded and reported.

    bad_uns = []
    for hom_hash in slopes_bad:
        for s in slopes_bad[hom_hash]:
            reason = (name, hom_hash, s, 'Could not verify hyperbolicity')
            verbose_print(verbose, 2, [reason])
            bad_uns.append(reason)

    for hom_hash in slopes_non_hyp:
        for s in slopes_non_hyp[hom_hash]:
            for t in slopes_non_hyp[hom_hash]:
                if t < s:
                    # We will have checked the pair (t, s) separately.
                    continue 
                if geom_tests.alg_int(s, t) == 0:
                    # Parallel slopes cannot be cosmetic.
                    continue

                s_name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
                t_name = fetch_exceptional_data(M, t, exceptions_table, "name", tries, verbose)

                reason = (name, s, t, s_name, t_name)
                verbose_print(verbose, 10, ["comparing", s_name, "to", t_name])

                # Rapid tests that require only s_name and t_name     

                if "#" in s_name or "#" in t_name:
                    if abs(geom_tests.alg_int(s,t)) > 1:
                        # Gordon and Luecke proved distance between reducible fillings must be 1.
                        verbose_print(verbose, 2, [s_name, t_name, "distinguished by Gordon-Luecke theorem on distance between reducible fillings"])
                        continue
                s_lens, _ = is_lens_space_from_name(s_name, verbose)
                t_lens, _ = is_lens_space_from_name(t_name, verbose)
                if s_name == "S2 x S1" or s_lens or t_name == "S2 x S1" or t_lens:
                    if abs(geom_tests.alg_int(s,t)) > 1:
                        # Cyclic surgery theorem
                        verbose_print(verbose, 2, [s_name, t_name, "distinguished by cyclic surgery theorem"])
                        continue
                
                if are_distinguished_closed_sfs(s_name, t_name, verbose):
                    continue
                if are_distinguished_graph_pairs(s_name, t_name, verbose):
                    continue
                 
                s_ator_sfs, s_geom, _, _ = fetch_exceptional_data(M, s, exceptions_table, "atoroidal_sfs", tries, verbose)
                t_ator_sfs, t_geom, _, _ = fetch_exceptional_data(M, t, exceptions_table, "atoroidal_sfs", tries, verbose)

                # Less rapid tests, which require the name of one manifold and normal surface theory on the other.

                if s_ator_sfs:
                    t_red, _ = fetch_exceptional_data(M, t, exceptions_table, "reducible", tries, verbose)
                    if s_geom != "S2 x R" and t_red:
                        # M(s) is irreducible but M(t) is reducible
                        continue
                    t_tor, _ = fetch_exceptional_data(M, t, exceptions_table, "toroidal", tries, verbose)
                    if t_tor:
                        # M(s) is atoroidal but M(t) is toroidal
                        continue                    
                if t_ator_sfs:
                    s_red, _ = fetch_exceptional_data(M, s, exceptions_table, "reducible", tries, verbose)
                    if t_geom != "S2 x R" and s_red:
                        # M(t) is irreducible but M(s) is reducible
                        continue                    
                    s_tor, _ = fetch_exceptional_data(M, s, exceptions_table, "toroidal", tries, verbose)
                    if s_tor:
                        # M(t) is atoroidal but M(s) is toroidal
                        continue
                
                # At this point, both manifolds should be reducible, or both toroidal (or we have failed to identify a SFS).

                # Tests that search for covers are pretty slow, but effective.                    
                if is_distinguished_by_covers(M, s, M, t, tries, verbose):
                    continue

                if is_distinguished_by_cover_homology(M, s, M, t, tries, verbose):
                    continue

                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)


    # Step three: initialize volume and systole. Get the systole-short hyperbolic slopes,
    # and split them by homology.

    volumes_table = {}  # Lookup table of volumes of hyperbolic fillings
    M_vol = fetch_volume(M, (0,0), volumes_table, tries, verbose)
                
    sys = geom_tests.systole_with_tries(M, tries=tries, verbose=verbose)
    verbose_print(verbose, 3, [name, 'systole is at least', sys])
    if sys == None:
        return [(name, None, None, None, 'systole fail')]
    
    norm_len_cutoff = max(9.97, sqrt((2*pi/sys) + 56.0).n(200)) 
    verbose_print(verbose, 4, [name, 'norm_len_cutoff', norm_len_cutoff])
               
    short_slopes = geom_tests.find_short_slopes(M, norm_len_cutoff, normalized=True, verbose=verbose)
                    
    verbose_print(verbose, 3, [name, len(short_slopes), 'short slopes found'])
    verbose_print(verbose, 5, short_slopes)

    # slopes_by_homology = {}
    for s in short_slopes:
        p = abs(geom_tests.alg_int(s, l_hom))
        if p == 0:
            verbose_print(verbose, 4, [name, 'removing homological longitude'])
            continue # the homological longitude is unique, so cannot be cosmetic
        N = M.copy()
        N.dehn_fill(s)
        hom_gp = str(N.homology())
        hom_hash = (p, hom_gp)  # Note that p is redunant by Lemma~\ref{Lem:HomologyTorsion}
        
        if hom_hash in slopes_non_hyp:
            if s in slopes_non_hyp[hom_hash]:
                verbose_print(verbose, 8, [name, s, 'known exceptional slope'])
                continue
        if hom_hash in slopes_bad:
            if s in slopes_bad[hom_hash]:
                verbose_print(verbose, 8, [name, s, 'known bad (unidentified) slope'])
                continue
        if hom_hash in slopes_hyp:
            if s in slopes_hyp[hom_hash]:
                verbose_print(verbose, 8, [name, s, 'known hyperbolic slope'])
                continue

        assert is_hyperbolic_filling(M, s, mer_hol, long_hol, exceptions_table, tries, verbose)
        # All slopes shorter than 6.01 should have been identified already. The new ones are hyperbolic.
        add_to_dict_of_sets(slopes_hyp, hom_hash, s)
            
    num_non_hyp_slopes = sum(len(slopes_non_hyp[hash]) for hash in slopes_non_hyp)
    num_bad_slopes = sum(len(slopes_bad[hash]) for hash in slopes_bad)
    num_hyp_slopes = sum(len(slopes_hyp[hash]) for hash in slopes_hyp)
    verbose_print(verbose, 3, [name, num_hyp_slopes, 'hyperbolic', num_non_hyp_slopes, 'exceptional', num_bad_slopes, 'bad'])
    verbose_print(verbose, 4, [name, len(slopes_hyp), 'homology buckets of hyperbolic slopes'])
    verbose_print(verbose, 5, [name, 'hyp slopes', slopes_hyp])
    verbose_print(verbose, 5, [name, 'non-hyp slopes', slopes_non_hyp])
    if len(slopes_bad) > 0:
        verbose_print(verbose, 0, [name, 'bad slopes', slopes_bad])

    # There is no step four.

    # Step five - Compute the max of the volumes in
    # slopes_hyp[hom_hash] and use this to compute the larger set of
    # "comparison slopes".

    max_volumes = {}
    for hom_hash in slopes_hyp:
        max_volumes[hom_hash] = max(fetch_volume(M, s, volumes_table, tries, verbose) for s in slopes_hyp[hom_hash])

    verbose_print(verbose, 5, [name, 'max volumes by homology', max_volumes])

    # len_m_hom = abs(m_hom[0]*mer_hol + m_hom[1]*long_hol)
    len_l_hom = abs(l_hom[0]*mer_hol + l_hom[1]*long_hol)
    slopes_low_volume = {}
    for hom_hash in slopes_hyp:
        verbose_print(verbose, 25, ['slopes hyp', slopes_hyp[hom_hash]])
        # M_vol is the volume of the unfilled manifold M
        l_max = HK_vol_bound_inv(M_vol - max_volumes[hom_hash]) * norm_fac # length on cusp
        if verbose > 25:
            print('hom_hash, max_vol[hom_hash]', hom_hash, max_volumes[hom_hash])
            print('l_max', l_max, 'l_max_normalized', HK_vol_bound_inv(M_vol - max_volumes[hom_hash]))
            print('normalized length endpoints', (l_max/norm_fac).endpoints(),)
            print('norm_fac', norm_fac.endpoints())
            print('len_l_hom', len_l_hom)

        p, hom_gp = hom_hash
        point = (p*m_hom[0], p*m_hom[1])
        middle = geom_tests.a_shortest_lattice_point_on_line(point, l_hom, mer_hol, long_hol)
        lower = int( (-l_max / len_l_hom).floor().lower() )
        upper = int( (l_max / len_l_hom).ceil().upper() )
        verbose_print(verbose, 25, ['lower, upper', lower, upper])
        for k in range(lower, upper + 1):
            verbose_print(verbose, 25, ['k', k])
            # move along the line 
            a = middle[0] + k * l_hom[0] 
            b = middle[1] + k * l_hom[1]
            t = geom_tests.preferred_rep((a, b))
            a, b = t
            verbose_print(verbose, 25, ['t', t])
            if gcd(a, b) > 1:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because gcd'])
                continue
            N = M.copy()
            N.dehn_fill(t)
            hom_gp_t = str(N.homology())
            if hom_gp_t != hom_gp:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because wrong homology'])
                continue
            # now we now that (p, hom_gp_t) are correct, so we can use the dictionaries we built
            if hom_hash in slopes_non_hyp and t in slopes_non_hyp[hom_hash]:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because non-hyp'])
                continue
            if hom_hash in slopes_bad and t in slopes_bad[hom_hash]:
                verbose_print(verbose, 25, [name, hom_hash, k, t, 'excluded because bad'])
                continue
            # Thus t is a hyperbolic filling, so 
            # First, check length
            verbose_print(verbose, 25, ['lengths', abs(a*mer_hol + b*long_hol), l_max])
            if abs(a*mer_hol + b*long_hol) <= l_max:
                # Then, check the volume
                t_vol = fetch_volume(M, t, volumes_table, tries, verbose)
                verbose_print(verbose, 25, ['t_vol', t_vol])
                verbose_print(verbose, 25, ['max_vol[hom_hash]', max_volumes[hom_hash]])
                if not t_vol > max_volumes[hom_hash]:   # We need the 'not' because we are comparing intervals
                    add_to_dict_of_sets(slopes_low_volume, hom_hash, t)
                    verbose_print(verbose, 25, ['added to slopes_low_volume'])
        # Sanity check: slopes_hyp[hom_hash] should be a subset of slopes_low_volume[hom_hash]
        for t in slopes_hyp[hom_hash]:
            assert t in slopes_low_volume[hom_hash]

    num_low_volume = sum(len(slopes_low_volume[hash]) for hash in slopes_low_volume)
    verbose_print(verbose, 3, [name, num_low_volume, 'low volume slopes found'])
    verbose_print(verbose, 5, [name, '(somewhat-)low volume slopes', slopes_low_volume])


    # Step six - check for hyperbolic cosmetic pairs.
    # That is: for all p, slopes s in slopes_hyp[hom_hash], and slopes t in
    # slopes_low_volume[hom_hash] (with s \neq t) show that M(s) is not
    # orientation-preservingly homeomorphic to M(t).  Collect
    # counterexamples and difficult cases to be returned to calling
    # function.

    for hom_hash in slopes_hyp:
        for s in slopes_hyp[hom_hash]:
            for t in slopes_low_volume[hom_hash]:
                if t in slopes_hyp[hom_hash] and t < s:
                    # since slopes_hyp[hom_hash] \subset
                    # slopes_low_volume[hom_hash] we have (or will)
                    # checked the pair (t, s) so skip!
                    continue 
                if geom_tests.alg_int(s,t) == 0:
                    continue
                s_vol = fetch_volume(M, s, volumes_table, tries, verbose)
                t_vol = fetch_volume(M, t, volumes_table, tries, verbose)
                verbose_print(verbose, 12, [M, s, t, s_vol, t_vol, 'volumes'])
                if s_vol > t_vol or t_vol > s_vol:
                    verbose_print(verbose, 6, [M, s, t, 'verified volume distinguishes'])
                    continue
                looks_distinct, rigorous = False, False
                if not check_chiral:
                    # Try to distinguish by oriented hyperbolic invariants
                    looks_distinct, rigorous = geom_tests.is_distinguished_by_hyp_invars(M, s, t, tries, verbose)
                    if looks_distinct and rigorous:
                        continue
                    
                if is_distinguished_by_covers(M, s, M, t, tries, verbose):
                    continue
                if is_distinguished_by_cover_homology(M, s, M, t, tries, verbose):
                    continue
                    
                if looks_distinct and not rigorous:
                    reason = (name, s, t, 'distinguished by non-rigorous length spectrum')
                if not looks_distinct:
                    reason = (name, s, t, 'Not distinguished by hyperbolic invariants or covers')
                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)

    verbose_print(verbose, 1, [name, 'non-distinguished pairs', bad_uns])
    
    return bad_uns
    

def check_mfds(manifolds, use_BoyerLines=True, tries=7, verbose=4, report=20):
    """
    Checks a list of manifolds for purely cosmetic surgeries.
    
    Returns two lists of pairs of slopes that the program could not distinguish:
    * amphichiral_uns is a list of undistinguished amphichiral pairs (M,s) and (M,t), where s,t
        are exchanged by an orientation-reversing symmetry of M, and M(s) looks similar to (M,t)
    * bad_uns is a list of pairs (M,s) and (M,t), where s,t are *not* exchanged by an orientation-
        reversing symmetry of M, and (M,s) looks similar to (M,t)
    """
    
    verbose_print(verbose, 12, ["entering check_mfds"])
    amphichiral_uns = []
    bad_uns = []
    for n, M in enumerate(manifolds):
        if type(M) is snappy.Manifold:
            name = M.name()
        if type(M) == str:
            name = M
            M = snappy.Manifold(name)
        uns = check_cosmetic(M, use_BoyerLines=use_BoyerLines, check_chiral=False, tries=tries, verbose=verbose)
        if len(uns) > 0:
            is_amph, cob = is_amphichiral(M, tries=tries, verbose=verbose)
            if is_amph:
                for line in uns:
                    s = line[1]
                    t = line[2]
                    filled_name = line[3]
                    if is_chiral_graph_mfd_from_name(filled_name) and geom_tests.preferred_rep(cob*vector(s)) == t:
                        # The slopes s and t are interchanged by symmetry, and the filled manifold is chiral
                        verbose_print(verbose, 2, ['chiral filling on amph manifold:', name, s, t, filled_name])
                        continue
                    else:
                        verbose_print(verbose, 0, ["undistinguished amphichiral filling", line])
                        amphichiral_uns.append(line)
            else:
                for line in uns:
                    verbose_print(verbose, 0, ["not amph", line])
                bad_uns.extend(uns)
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n])
            verbose_print(verbose, 0, [amphichiral_uns])
            verbose_print(verbose, 0, [bad_uns])
    return amphichiral_uns, bad_uns


def check_mfds_chiral(manifolds, tries=7, verbose=4, report=20):
    """
    Checks a list of manifolds for both purely and chirally cosmetic surgeries.
    
    Returns a list of amphichiral manifolds (which are not checked) and a list of pairs 
    of slopes (M,s) and (M,t), where M is chiral, such that the program could not 
    distinguish M(s) from M(t).
    
    This routine is designed to be used for chiral parent manifolds.
    Amphichiral parent manifolds are discarded, because they have infinitely
    many pairs of chirally cosmetic surgeries, of the form M(s) and M(-s).
    
    We note that if M is amphichiral, and M(s),M(t) are a chirally cosmetic pair,
    then M(s), M(-t) will be a purely cosmetic pair. Thus any "exotic" chirally cosmetic
    pair of slopes can still be found by running M through check_mfds(...).
    """
    
    verbose_print(verbose, 12, ["entering check_mfds_chiral"])
    bad_uns = []
    amphichiral_uns = []
    for n, M in enumerate(manifolds):
        if type(M) is snappy.Manifold:
            name = M.name()
        if type(M) == str:
            name = M
            M = snappy.Manifold(name)

        sol_type = M.solution_type()
    
        if sol_type != 'all tetrahedra positively oriented' and sol_type != 'contains negatively oriented tetrahedra':
            # So M is probably not a hyperbolic manifold. Try to identify it.
            
            kind, found_name = dunfield.identify_with_bdy_from_isosig(M)
            if kind != 'unknown':
                verbose_print(verbose, 2, [name, kind, found_name])
                bad_uns.append((name, None, None, found_name))
            elif is_exceptional_due_to_volume(M, verbose):   
                verbose_print(verbose, 2, [name, 'NON-RIGOROUS TEST says volume is too small']) 
                bad_uns.append((name, None, None, 'small volume'))
            else:
                verbose_print(verbose, 2, [M, 'bad solution type for unclear reasons.'])
                bad_uns.append((name, None, None, 'bad solution type for unclear reasons'))
            continue

        is_amph, cob = is_amphichiral(M, tries=tries, verbose=verbose)
        if is_amph:
            verbose_print(verbose, 2, [name, "is amphichiral; skipping."])
            amphichiral_uns.append(name)
            continue
        uns = check_cosmetic(M, use_BoyerLines=False, check_chiral=True, tries=tries, verbose=verbose)
        bad_uns.extend(uns)
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n])
            verbose_print(verbose, 0, ['Amphichiral mfds:', amphichiral_uns])
            verbose_print(verbose, 0, ['Bad slopes:', bad_uns])
    return amphichiral_uns, bad_uns


def check_using_lengths(slopelist, cutoff=3.1, verbose=4, report=20):
    """
    Given a list of tuples of the form (M,s,t) where M is a manifold (or a name) and s,t
    are slopes, checks to see whether M(s) can be distinguished from M(t) using
    geodesic length spectra up to a large cutoff. 
    
    This program tries to distinguish M(s) from M(t) as unoriented manifolds.
    
    We presume that M and M(s), M(t) are all hyperbolic.
    
    Returns a list of tuples that could not be distinguished.
    """
    
    verbose_print(verbose, 12, ["entering check_using_lengths"])
    bad_uns = []
    for n, line in enumerate(slopelist):
        M, s, t = line
        if type(M) is snappy.Manifold:
            name = M.name()
        if type(M) == str:
            name = M
            M = snappy.Manifold(name)

        sol_type = M.solution_type()
    
        if sol_type != 'all tetrahedra positively oriented' and sol_type != 'contains negatively oriented tetrahedra':
            verbose_print(verbose, 2, [M, 'bad solution type for unclear reasons.'])
            bad_uns.append((name, None, None, 'bad solution type for unclear reasons'))
            continue
            
        distinct = geom_tests.is_distinguished_by_length_spectrum(M, s, t, check_chiral=True, cutoff = cutoff, verbose=verbose)
        if not distinct:
            verbose_print(verbose, 4, [M, s, t, 'not distinguished by length spectrum up to', cutoff])
            bad_uns.append((name, s, t, 'not distinguished by length spectrum up to '+str(cutoff) ))
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n])
            verbose_print(verbose, 0, [bad_uns])
    return bad_uns
           
            
