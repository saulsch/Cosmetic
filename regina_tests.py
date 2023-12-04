#
# regina_tests.py
#

# This file contains utility code that applies various topological tests
# for identifying and distinguishing manifolds using regina and regina names.
# (which are often a list of Seifert invariants).

import snappy
import regina
import dunfield

from verbose import verbose_print

# Math 

from sage.functions.other import sqrt, ceil, floor
from sage.arith.misc import gcd, xgcd, factor, next_prime
from sage.symbolic.constants import pi
from sage.symbolic.ring import SR
from sage.modules.free_module_element import vector
from sage.rings.real_mpfr import RR
from sage.rings.real_mpfi import RIF
from sage.rings.rational_field import QQ



# wrappers for Regina utilities


def is_reducible_wrapper(M, tries=10, verbose=3):
    """
    Given a snappy Manifold M, presumed to be closed, uses
    Regina to decide whether M is reducible.
    Returns a Boolean and the list of summands, if true.
    """
    verbose_print(verbose, 12, [M, 'entering is_reducible_wrapper'])
    isosigs = dunfield.closed_isosigs(M, tries = 25, max_tets = 50)
    if isosigs == []:
        return (None, None)
    T = dunfield.to_regina(isosigs[0])
    irred = T.isIrreducible()
    if irred:
        out = (False, None)
        verbose_print(verbose, 12, [M, out, 'from is_reducible_wrapper'])
        return out
    else:
        name = dunfield.regina_name(M)
        out = (True, dunfield.regina_name(M))
        assert "#" in name
        verbose_print(verbose, 12, [M, out, 'from is_reducible_wrapper'])
        return out
    

def is_toroidal_wrapper(M, verbose=3):
    """
    Given a snappy manifold M, which could be cusped or closed,
    uses Regina to decide whether M is toroidal.
    Returns a Boolean and a list of two pieces (not necessarily minimal).
    """    
    verbose_print(verbose, 12, [M, 'entering is_toroidal_wrapper'])
    N = M.filled_triangulation() # this is harmless for a cusped manifold
    T = regina.Triangulation3(N) 
    T.simplifyToLocalMinimum() # this makes it more likely to be zero-efficient
    out = dunfield.is_toroidal(T) # returns a boolean and the JSJ decomposition (if true)
    verbose_print(verbose, 6, [M, out, 'from is_toroidal_wrapper'])
    return out


def torus_decomp_wrapper(M, tries=10, verbose=3):
    """
    Given a snappy Manifold M, presumed to be closed, uses
    Regina to decide whether M is toroidal.
    Returns a Boolean and a list of pieces, if true.
    
    The list of pieces may not be the JSJ decomposition.
    Compare docstring for dunfield.decompose_along_tori.
    """
    verbose_print(verbose, 12, [M, 'entering torus_decomp_wrapper'])
    isosigs = dunfield.closed_isosigs(M, tries = 25, max_tets = 50)
    if isosigs == []:
        return (None, None) # we do not continue, because the normal surface theory may be too slow.
    out = (None, None)
    verbose_print(verbose, 25, isosigs)
    for i in range(min(len(isosigs), tries)):                                     
        try:
            T = dunfield.to_regina(isosigs[i])
            out = dunfield.decompose_along_tori(T)                                                                   
            if out[0] == True or out[0] == False:
                break
        except Exception as e:
            verbose_print(verbose, 6, [M, isosigs[i], e])

    verbose_print(verbose, 6, [M, out, 'from torus_decomp_wrapper'])
    return out



# Identifying and distinguishing graph manifolds using Regina names

def is_lens_space_from_name(name, verbose=3):
    """
    Given a regina name, decide if it is a lens
    space and extract the coefficients.  
    
    Returns a Boolean and a tuple of integers:
    * Boolean is True if lens, and False if not
    * Tuple is (p,q) for lens space L(p,q)
    
    For our purposes, S2 x S1 is not a lens space.
    """

    verbose_print(verbose, 12, ["Entering is_lens_space_from_name"])
    if name == None:
        return (None, None)
        
    if name == "S3":
        return (True, [1, 0])
    if name == "RP3":
        return (True, [2, 1])
        
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
    computes and returns the Euler number.
    If the ModOne flag is True, then reduce the Euler number modulo 1.
    """
    eul = sum( QQ((q, p)) for (p, q) in coeffs )
    if ModOne:
        return eul - floor(eul)
    else:
        return eul
        
        
def euler_char(starting_char, coeffs):
    """
    Given starting_char (the Euler characteristic of the total space of the base
    2-orbifold, ignoring singular fibers) and coeffs (the vector of coefficients
    of singular fibers), returns the Euler characteristic of the base orbifold.
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
        
    verbose_print(verbose, 12, ["Entering is_closed_sfs_from_name"])

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

    verbose_print(verbose, 12, ["Entering is_sfs_over_disk_from_name"])

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
    """
    Given two Regina names, checks whether the two manifolds are lens spaces.
    If yes, and the two are not homeomorphic, return True. If one is not
    a lens space, or they are homeomorphic, return False.
    This only tests for _un_oriented homeomorphism.
    """
    
    verbose_print(verbose, 12, ["Entering are_distinguished_lens_spaces"])
    bool0, ints0 = is_lens_space_from_name(name0, verbose=verbose)
    bool1, ints1 = is_lens_space_from_name(name1, verbose=verbose)
    if not (bool0 and bool1):
        verbose_print(verbose, 10, [name0, name1, "at least one is not a lens space"])
        return False
    p0, q0 = ints0
    p1, q1 = ints1
    if p0 != p1:
        verbose_print(verbose, 4, [name0, name1, "lens spaces with different homology"])
        return True
    p = p0
    if ((q0 - q1) % p) == 0 or ((q0 + q1) % p) == 0 or ((q0 * q1) % p) == 1 or ((q0 * q1) % p) == -1 % p:
        verbose_print(verbose, 10, [name0, name1, "homeomorphic lens spaces"])
        return False
    verbose_print(verbose, 10, [name0, name1, "non-homeomorphic lens spaces"])
    return True


def are_distinguished_closed_sfs(name_0, name_1, verbose = 3):
    """
    Given two Regina names, checks whether the two manifolds are SFS over S2,
    RP2, Torus, or Klein Bottle.
    If yes, and the two are not homeomorphic, return True. 
    Lens spaces are allowed, and are handled separately from others over S2.
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    This routine only tests for _un_oriented homeomorphism.
    """

    verbose_print(verbose, 12, ["Entering are_distinguished_closed_sfs"])
    
    bool_0, geom_0, base_0, coeffs_0 = is_closed_sfs_from_name(name_0, verbose=verbose)
    bool_1, geom_1, base_1, coeffs_1 = is_closed_sfs_from_name(name_1, verbose=verbose)
    
    if not (bool_0 and bool_1):
        verbose_print(verbose, 10, [name_0, name_1, "at least one seems not to be a known closed SFS"])
        return False
        
    if base_0 != base_1:
        verbose_print(verbose, 10, [name_0, name_1, "different base orbifolds"])
        return True
        
    if geom_0 != geom_1:
        verbose_print(verbose, 10, [name_0, name_1, "different geometric types"])
        return True

    if geom_0 == "Lens" and geom_1 == "Lens":
        return are_distinguished_lens_spaces(name_0, name_1, verbose = verbose)
        
    # At this point, we know that both are SFS over the same base, and neither is a lens space.
   
    coeffs_0.sort()
    coeffs_1.sort()

    if len(coeffs_0) != len(coeffs_1):
        verbose_print(verbose, 10, [name_0, name_1, "different number of singular fibers"])
        return True

    cone_pts_0 = [p for (p, q) in coeffs_0]
    cone_pts_1 = [p for (p, q) in coeffs_1]

    if cone_pts_0 != cone_pts_1: 
        verbose_print(verbose, 10, [name_0, name_1, "base orbifolds have different cone points"])
        return True

    eul_num_0 = euler_num(coeffs_0)
    eul_num_1 = euler_num(coeffs_1)
    
    if abs(eul_num_0) != abs(eul_num_1): 
        verbose_print(verbose, 10, [name_0, name_1, "Euler numbers are different"])
        return True

    # normed_coeffs_0 = [(p, q % p) for p, q in coeffs_0].sort()
    # normed_coeffs_1 = [(p, q % p) for p, q in coeffs_1].sort()
    # if normed_coeffs_0 != normed_coeffs_1: 
    #    verbose_print(verbose, 12, [name_0, name_1, "distinguished by singular fibers"])
    #    return True

    verbose_print(verbose, 10, [name_0, name_1, "could not distinguish."])
    return False


def are_distinguished_sfs_over_disk(name_0, name_1, verbose = 3):
    """
    Given two Regina names, checks whether the two manifolds are SFS over disk.
    If yes, and the two are not homeomorphic, return True. 
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    This routine only tests for _un_oriented homeomorphism.
    """

    bool_0, coeffs_0 = is_sfs_over_disk_from_name(name_0)
    bool_1, coeffs_1 = is_sfs_over_disk_from_name(name_1)
    coeffs_0.sort()
    coeffs_1.sort()

    if not (bool_0 and bool_1):
        verbose_print(verbose, 10, [name_0, name_1, "at least one seems not to be a sfs over disk"])
        return False 

    if len(coeffs_0) != len(coeffs_1):
        verbose_print(verbose, 10, [name_0, name_1, "different number of singular fibers"])
        return True

    cone_pts_0 = [p for (p, q) in coeffs_0]
    cone_pts_1 = [p for (p, q) in coeffs_1]

    if cone_pts_0 != cone_pts_1: 
        verbose_print(verbose, 10, [name_0, name_1, "base orbifolds are different"])
        return True

    euler_num_0 = euler_num(coeffs_0, ModOne = True)
    euler_num_1 = euler_num(coeffs_1, ModOne = True) 
    if (euler_num_0 != euler_num_1) and (euler_num_0 + euler_num_1 != 1): 
        verbose_print(verbose, 10, [name_0, name_1, "euler numbers are different", euler_num_0, euler_num_1])
        return True

    # normed_coeffs_0 = [(p, q % p) for p, q in coeffs_0].sort()
    # normed_coeffs_1 = [(p, q % p) for p, q in coeffs_1].sort()
    # if normed_coeffs_0 != normed_coeffs_1: 
    #    verbose_print(verbose, 12, [name_0, name_1, "distinguished by singular fibers"])
    #    return True

    verbose_print(verbose, 10, [name_0, name_1, "could not distinguish."])
    return False


def are_distinguished_graph_pairs(name_0, name_1, verbose = 3):
    """
    Given two Regina names, checks whether the two manifolds are graph pairs.
    If yes, and the two are not homeomorphic, return True. 
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    According to Regina documentation, a graph pair is guaranteed to not be a SFS, so the list
    of pieces is an invariant.
    This routine only tests for _un_oriented homeomorphism.
    """

    bool_0, pieces_0 = is_graph_pair_from_name(name_0)
    bool_1, pieces_1 = is_graph_pair_from_name(name_1)

    if not (bool_0 and bool_1):
        verbose_print(verbose, 10, [name_0, name_1, "at least one seems not to be a graph pair"])
        # so give up
        return False 

    if are_distinguished_sfs_over_disk(pieces_0[0], pieces_1[0]) and are_distinguished_sfs_over_disk(pieces_0[0], pieces_1[1]):
        verbose_print(verbose, 10, [pieces_0[0], 'is not a piece of', name_1])
        return True

    if are_distinguished_sfs_over_disk(pieces_0[1], pieces_1[0]) and are_distinguished_sfs_over_disk(pieces_0[1], pieces_1[1]):
        verbose_print(verbose, 10, [pieces_0[1], 'is not a piece of', name_1])
        return True

    if are_distinguished_sfs_over_disk(pieces_1[0], pieces_0[0]) and are_distinguished_sfs_over_disk(pieces_1[0], pieces_0[1]):
        verbose_print(verbose, 10, [pieces_1[0], 'is not a piece of', name_0])
        return True

    if are_distinguished_sfs_over_disk(pieces_1[1], pieces_0[0]) and are_distinguished_sfs_over_disk(pieces_1[1], pieces_0[1]):
        verbose_print(verbose, 10, [pieces_1[1], 'is not a piece of', name_0])
        return True

    # We could also check the gluing matrices. We do not do this.

    verbose_print(verbose, 10, [name_0, name_1, "could not distinguish."])
    return False


def is_chiral_graph_mfd_from_name(name, verbose = 3):
    """
    Given the Regina name of a graph manifold M assembled from Seifert fibered pieces,
    try a few tests to determine whether M is chiral. If chiral, return True.
    If the simple tests do not succeed, return None.
    The tests applied here are not exhaustive, but a True answer is trustworthy.
    """

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