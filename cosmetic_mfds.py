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


def is_lens_space_from_name(name):
    """
    Given a regina name, parses it enough to decide if it is a lens
    space and then extracts the coefficients.  
    """
    if name == "S3":
        return (True, [1, 0])
    if name == "RP3":
        return (True, [2, 1])
    if name == "S2 x S1":
        return (True, [0, 1])
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
    return (True, ints)



def is_sfs_over_s2_from_name(name):
    """
    Given a regina name, if it is a SFS over S^2 (and not a lens
    space) return True and the coefficients.
    """
    # Note that we don't count lens spaces as SFSs. 
    if not "SFS [S2: (" == name[:10]:
        return (None, None)
    if "#" in name:
        return (None, None)
    name = name[9:-1] # regina names...
    coeffs = name.split(" ")
    assert len(coeffs) > 2
    coeffs = [coeff.strip("(") for coeff in coeffs]
    coeffs = [coeff.strip(")") for coeff in coeffs]
    coeffs = [coeff.split(",") for coeff in coeffs]
    coeffs = [[int(p) for p in coeff] for coeff in coeffs]
    return (True, coeffs)


def is_sfs_over_disk_from_name(name):
    """
    Given a regina name, if it is a SFS over D^2 (and not a solid torus),
    return True and the coefficients. If not, or unsure, return (None, None).
    """
    
    if not "SFS [D: (" == name[:9]:
        return (None, None)
    if "#" in name:
        return (None, None)
    if "U/m" in name:
        return (None, None)
    name = name[8:-1] # regina names...
    coeffs = name.split(" ")
    assert len(coeffs) > 1
    coeffs = [coeff.strip("(") for coeff in coeffs]
    coeffs = [coeff.strip(")") for coeff in coeffs]
    coeffs = [coeff.split(",") for coeff in coeffs]
    coeffs = [[int(p) for p in coeff] for coeff in coeffs]
    return (True, coeffs)


def is_graph_pair_from_name(name):
    """
    Given a regina name, test to see if it is a graph manifold with exactly two pieces,
    each of which is SFS over a disk. If so, return True and the pieces.
    According to Regina documentation, a True answer guarantees that the manifold is not
    a SFS, because the gluing matrix does not send fibers to fibers.
    If not, or unsure, return (None, None).
    """
    
    if "#" in name:
        return (None, None)
    tori = name.count("U/m")
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
    
    bool0, ints0 = is_lens_space_from_name(name0)
    bool1, ints1 = is_lens_space_from_name(name1)
    if not (bool0 and bool1):
        verbose_print(verbose, 12, [name0, name1, "at least one is not a lens space"])
        return False
    p0, q0 = ints0
    p1, q1 = ints1
    if p0 != p1:
        verbose_print(verbose, 0, [name0, name1, "lens spaces with different homology"])
        # verbose threshold is low because we expect this to never happen.  [grin]
        return True
    p = p0
    if ((q0 - q1) % p) == 0 or ((q0 + q1) % p) == 0 or ((q0 * q1) % p) == 1 or ((q0 * q1) % p) == -1 % p:
        verbose_print(verbose, 12, [name0, name1, "homeomorphic lens spaces"])
        return False
    verbose_print(verbose, 12, [name0, name1, "non-homeomorphic lens spaces"])
    return True


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


def are_distinguished_sfs_over_s2(name_0, name_1, verbose = 3):
    '''
    Given two Regina names, checks whether the two manifolds are SFS over S2.
    If yes, and the two are not homeomorphic, return True. 
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    This routine only tests for _un_oriented homeomorphism.
    '''
    
    bool_0, coeffs_0 = is_sfs_over_s2_from_name(name_0)
    bool_1, coeffs_1 = is_sfs_over_s2_from_name(name_1)
    coeffs_0.sort()
    coeffs_1.sort()

    if not (bool_0 and bool_1):
        verbose_print(verbose, 12, [name_0, name_1, "at least one seems not to be a sfs over s2"])
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

    eul_num_0 = euler_num(coeffs_0)
    eul_num_1 = euler_num(coeffs_1)
    
    if abs(eul_num_0) != abs(eul_num_1): 
        verbose_print(verbose, 12, [name_0, name_1, "euler numbers are different"])
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
    is_lens, ints = is_lens_space_from_name(name)
    if is_lens:
        p, q = ints
        return ((q**2 + 1) % p) != 0
    
    is_sfs_over_s2, coeffs = is_sfs_over_s2_from_name(name)
    if is_sfs_over_s2:
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

    is_sfs_over_disk, coeffs = is_sfs_over_disk_from_name(name)
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


def is_distinguished_by_covers(M, s, t, tries, verbose):
    """
    Given a snappy manifold M and a pair of slopes s and t, builds
    M(s) and M(t), computes a collection of covers of each, counts
    them, and returns True if the "spectrum" distinguishes.  If this
    fails, returns False.
    """
    Ms = M.copy()
    Mt = M.copy()
    Ms.dehn_fill(s)
    Mt.dehn_fill(t)

    Ms_covers = [len(Ms.covers(i)) for i in range(2, 6)]
    Mt_covers = [len(Mt.covers(i)) for i in range(2, 6)]

    if Ms_covers != Mt_covers:
        verbose_print(verbose, 6, [M, s, t, 'cover spectrum distinguishes'])
        return True

    return False

    
def is_distinguished_by_cover_homology(M, s, t, tries, verbose):
    """
    Given a snappy manifold M and a pair of slopes s and t, builds
    M(s) and M(t), computes a collection of covers of each, computes
    the homology groups of those covers and finally returns True if that
    invariant distinguishes.  If this fails, returns False.
    """
    Ms = M.copy()
    Mt = M.copy()
    Ms.dehn_fill(s)
    Mt.dehn_fill(t)

    if Ms.homology() != Mt.homology():
        # This was not supposed to happen, but does because half-lives-half-dies only works over Q. 
        verbose_print(verbose, 5, [Ms, Ms.homology(), ',', Mt, Mt.homology(), 'distinguished by homology groups'])
        return True

    order = order_of_torsion(Ms)
    if order == 1:
        # urk
        verbose_print(verbose, 5, [Ms, Mt, "are Z homology three-spheres. Cool!"])
        return False
    factors = list(factor(order))
    factors = [f[0] for f in factors] # strip the powers
    factors.sort()
    
    p = factors[0] # smallest prime
    # first, try covers of degree exactly p
    if p < tries:
        distinct = check_cover_homology_fixed_deg(Ms, Mt, p, verbose)
        if distinct:
            return True

    # Saul: I don't think this can work... Don't the covers have to
    # have degree dividing the above?  Hmm. Perhaps there is profit
    # lurking in degree four and six fold covers?  Any way, we
    # hopefully do not spend too much time making covers...
    cap = min(tries, 8) # do not bother with covers of degree more than 8
    for deg in range(cap):
        distinct = check_cover_homology_fixed_deg(Ms, Mt, deg, verbose)
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
    
    allowed_fields = ["fund_gp", "name", "lens", "sfs_over_s2", "reducible", "toroidal"]
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
            verbose_print(verbose, -1, [N, "could not compute name"])
            return None

    if field == "lens":
        name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
        if name == None:
            return (None, None)

        out = is_lens_space_from_name(name)
        is_lens, _ = out
        if is_lens: 
            exceptions_table[s]["lens"] = out
            verbose_print(verbose, 10, [N, name, 'lens coeffs added to table'])
            return out
        else:
            verbose_print(verbose, 10, [N, name, 'no lens coeffs found'])
            return out
    
    if field == "sfs_over_s2":
        name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
        if name == None:
            return (None, None)

        out = is_sfs_over_s2_from_name(name)
        is_sfs_over_s2, _ = out
        if is_sfs_over_s2: 
            exceptions_table[s]["sfs_over_s2"] = out
            verbose_print(verbose, 10, [N, name, 'sfs coeffs added to table'])
            return out
        else:
            verbose_print(verbose, 10, [N, s, name, 'no sfs coeffs found'])
            return out
        
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
        
        
### Dave checked code to here - 2021/07/15

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
        
        # verbose_print(verbose, 10, [N, 'computing verified volume'])
        # for i in range(tries):
        #     # for next time - we should be willing to take covers someplace here.  
        #     try:    
        #         volumes_table[s] = P.volume(verified = True, bits_prec=prec)
        #         return volumes_table[s]
        #     except RuntimeError: # hackedy-hack
        #         verbose_print(verbose, 5, [N, 'Volume computation failed at precision', prec])
        #         prec = prec*2
        # # Now, all attempts to find volume have failed
        # print(N, 'putting untrusted volume in the table')
        # R = RealIntervalField(10) # downgrade the precision!                                       
        # volumes_table[s] = R(N.volume())
        # return volumes_table[s]


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



def check_cosmetic(M, use_BoyerLines, tries=8, verbose=5):
    '''
    Given a one-cusped manifold M we equip it with a shortest framing
    and then return a list of tuples - (name, s, t, 'reason') where s
    and t are possibly a cosmetic pair.
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

    if use_BoyerLines:
        h = M.homology()
        if h.betti_number() == 1 and h.rank() == 1:
            # M is the complement of a knot in an integer homology sphere
            if Casson_invt(M, verbose) != 0:
                # The second derivative of the Alexander polynomial at 1 is nonzero,
                # so M has no cosmetic surgeries by Boyer-Lines
                verbose_print(verbose, 2, [M, 'has no cosmetic surgeries by Boyer-Lines'])
                return []

    # Before we try to think _too_ deeply, we check if the geometric
    # structure is good enough.

    sol_type = M.solution_type()
    
    if sol_type != 'all tetrahedra positively oriented' and sol_type != 'contains negatively oriented tetrahedra':
        # So M is probably not a hyperbolic knot.  Let's do a few
        # quick tests to help ourselves later, and then give up.

        if geom_tests.is_torus_link_filling(M, verbose):
            # M is a torus knot, so it has non-zero tau invariant, and
            # so by Ni-Wu satisfies the cosmetic surgery conjecture
            verbose_print(verbose, 3, [M.name(), 'is a torus knot; no cosmetic surgeries by Ni-Wu'])
            # Note: torus knots should get caught by the Casson_invt test above, so we should
            # not end up in this branch.
            return []
        out = geom_tests.is_toroidal_wrapper(M, verbose)
        if out[0]:
            # M is a satellite so use the torus decomposition as the 'reason'
            verbose_print(verbose, 3, [name, 'is toroidal'])
            return [(name, None, None, 'toroidal mfd: ' + str(out[1]))]
        # Anything else is confusing
        if is_exceptional_due_to_volume(M, verbose):   
            verbose_print(verbose, 2, [name, 'NON-RIGOROUS TEST says volume is too small']) 
            return [(name, None, None, 'small volume')]
        verbose_print(verbose, 2, [M, 'bad solution type for unclear reasons...'])
        return [(name, None, None, 'bad solution type - strange!')]
                
    # Ok, at this point we are probably hyperbolic.

    # Step zero - Install a good hyperbolic metric. Find the volume and systole. 

    M = dunfield.find_positive_triangulation(M, tries=tries, verbose=verbose)

    volumes_table = {}  # Lookup table of volumes of hyperbolic fillings
    M_vol = fetch_volume(M, (0,0), volumes_table, tries, verbose)
    exceptions_table = {}  # Lookup table of information about non-hyperbolic fillings
        
    for i in range(2*tries): # that looks like a magic number... 
        try:
            N = M.copy()
            for j in range(i):
                N.randomize()
            sys = geom_tests.systole(M, verbose = verbose)
            break
        except:
            sys = None
            verbose_print(verbose, 10, [N, 'systole failed on attempt', i])
        
    if sys == None:
        verbose_print(verbose, 2, [name, None, None, 'systole fail'])
        return [(name, None, None, 'systole fail')]

    verbose_print(verbose, 3, [name, 'systole is at least', sys])
    # norm_len_cutoff = max(10.1, sqrt((2*pi/sys) + 58.0).n(200))
    norm_len_cutoff = max(9.97, sqrt((2*pi/sys) + 56.0).n(200)) 
    verbose_print(verbose, 4, [name, 'norm_len_cutoff', norm_len_cutoff])
    
    # Step one - fix the framing and gather the invariants that can
    # be found rigorously.

    # Switch to low precision to save time now. 
    M.set_peripheral_curves('shortest')
    # C = M.cusp_neighborhood()
    # C.set_displacement(C.stopping_displacement())
    mer_hol, long_hol, norm_fac = geom_tests.cusp_invariants(M)
    l_hom = geom_tests.preferred_rep(M.homological_longitude())
    m_hom = geom_tests.shortest_complement(l_hom, mer_hol, long_hol)
    
    verbose_print(verbose, 4, [name, 'cusp_stuff', 'merid', mer_hol, 'long', long_hol])
    verbose_print(verbose, 5, ['cusp_stuff', 'norm_fac', norm_fac, 'homolog. long.', l_hom, 'homolog. merid.', m_hom])
    
    # Step two - get the short slopes. Split them by homology
           
    short_slopes = geom_tests.find_short_slopes(M, norm_len_cutoff, normalized=True, verbose=verbose)
                    
    verbose_print(verbose, 3, [name, len(short_slopes), 'short slopes found'])
    verbose_print(verbose, 5, short_slopes)

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

    verbose_print(verbose, 5, [name, 'slopes_by_homology', slopes_by_homology])
        
    # Step three - there is no step three.
    
    # Step four - split slopes_by_homology into slopes_hyp, slopes_non_hyp, slopes_bad

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

    # Temporary off-ramp
    # return []

    # Step six - check for cosmetic pairs in slopes_non_hyp[hom_hash].
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
                    # we have (or will) checked the pair (t, s) so
                    continue 
                if geom_tests.alg_int(s, t) == 0:
                    # parallel slopes can't be distinguished so
                    continue

                s_name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
                t_name = fetch_exceptional_data(M, t, exceptions_table, "name", tries, verbose)

                reason = (name, s, t, s_name, t_name)

                # TODO: simplify the logic in the next batch of tests

                if s_name == t_name:
                    # give up
                    bad_uns.append(reason)
                    continue
                
                s_lens, _ = fetch_exceptional_data(M, s, exceptions_table, "lens", tries, verbose)
                t_lens, _ = fetch_exceptional_data(M, t, exceptions_table, "lens", tries, verbose)

                if s_lens and t_lens:
                    if are_distinguished_lens_spaces(s_name, t_name, verbose):
                        continue
                    else:
                        verbose_print(verbose, 2, [reason])
                        bad_uns.append(reason)
                        continue

                s_sfs, _ = fetch_exceptional_data(M, s, exceptions_table, "sfs_over_s2", tries, verbose)
                t_sfs, _ = fetch_exceptional_data(M, t, exceptions_table, "sfs_over_s2", tries, verbose)

                if (s_lens and t_sfs) or (s_sfs and t_lens):
                    continue

                if s_sfs and t_sfs:
                    if are_distinguished_sfs_over_s2(s_name, t_name, verbose):
                        continue
                    else:
                        verbose_print(verbose, 2, [reason])
                        bad_uns.append(reason)
                        continue

                if s_lens or s_sfs:
                    t_red, _ = fetch_exceptional_data(M, t, exceptions_table, "reducible", tries, verbose)
                    if t_red:
                        continue
                    t_tor, _ = fetch_exceptional_data(M, t, exceptions_table, "toroidal", tries, verbose)
                    if t_tor:
                        continue
                    
                if t_lens or t_sfs:
                    s_red, _ = fetch_exceptional_data(M, s, exceptions_table, "reducible", tries, verbose)
                    if s_red:
                        continue                    
                    s_tor, _ = fetch_exceptional_data(M, s, exceptions_table, "toroidal", tries, verbose)
                    if s_tor:
                        continue

                if are_distinguished_graph_pairs(s_name, t_name, verbose):
                    continue

                # more tests here
                    
                if is_distinguished_by_covers(M, s, t, tries, verbose):
                    continue

                if is_distinguished_by_cover_homology(M, s, t, tries, verbose):
                    continue

                # or here

                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)


    # Step seven - check for hyperbolic cosmetic pairs.
    # That is: for all p, slopes s in slopes_hyp[hom_hash], and slopes t in
    # slopes_low_volume[hom_hash] (with s \neq t) show that M(s) is not
    # orientation-preservingly homeomorphic to M(t).  Collect
    # counterexamples and difficult cases to be returned to calling
    # function.


    # Uncomment the following to skip actual cosmetic checks
    # return bad_uns
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
                looks_distinct, rigorous = geom_tests.is_distinguished_by_hyp_invars(M, s, t, tries, verbose)
                if looks_distinct and rigorous:
                    continue
                    
                if is_distinguished_by_covers(M, s, t, tries, verbose):
                    continue
                if is_distinguished_by_cover_homology(M, s, t, tries, verbose):
                    continue
                    
                if looks_distinct and not rigorous:
                    reason = (name, s, t, 'distinguished by non-rigorous length spectrum')
                if not looks_distinct:
                    reason = (name, s, t, 'Not distinguished by hyperbolic invariants')
                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)

    verbose_print(verbose, 1, [name, 'non-distinguished pairs', bad_uns])
    
    return bad_uns
    
def check_mfds(manifolds, use_BoyerLines=True, tries=8, verbose=5, report=20):
    verbose_print(verbose, 12, ["entering check_mfds"])
    amphichiral_uns = []
    bad_uns = []
    for n, M in enumerate(manifolds):
        if type(M) is snappy.Manifold:
            name = M.name()
        if type(M) == str:
            name = M
            M = snappy.Manifold(name)
        uns = check_cosmetic(M, use_BoyerLines, tries=tries, verbose=verbose)
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

