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
import geom_tests as gt
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
from sage.interfaces.gap import gap

# Globals

six_theorem_length = 6.01 # All exceptionals shorter than this


# coding


def add_to_dict_of_sets(dictionary, key, value):
    if key not in dictionary:
        dictionary[key] = set([value])
    else:
        dictionary[key].add(value)
    return None


# Container for passing manifold data around

def enhance_manifold(M, tries = 8, verbose = 4):
    """
    Given a snappy manifold M, equipped with the preferred framing,
    install the geometric framing, record the original slopes, and
    record various slope data in M as methods.
    """

    # Fix the framing on the copy N to be shortest
    cob = M.set_peripheral_curves('shortest', return_matrices = True)
    # but remember the original meridian and longitude.
    M.meridian = cob[0][0]   # Original user-specified meridian
    M.longitude = cob[0][1]  # Original user-specified longitude

    # The following are holonomies in the new (shortest) framing
    M.mer_hol, M.long_hol, M.norm_fac = gt.cusp_invariants(M)
    M.l_hom = gt.preferred_rep(M.homological_longitude())
    M.m_hom = gt.shortest_complement(M.l_hom, M.mer_hol, M.long_hol) 
    
    M.exceptions_table = {}  # Dictionary of information about non-hyperbolic fillings
    M.slopes_non_hyp = set() # Confirmed non-hyperbolic slopes
    M.slopes_bad = set()     # Unidentified slopes (could be hyperbolic or exceptional)
    M.slopes_exclude = set() # The union of non_hyp and bad slopes. Exclude these from hyperbolic techniques
    M.volumes_table = {}     # Dictionary of volumes of hyperbolic fillings
    
    M.sys = None
    M.slopes_hyp = {}        # Dictionary of hyperbolic systole-short slopes, organized by homology
        
    return None


# Finding sets of slopes that satisfy various properties

def find_exceptionals(M, tries=8, verbose=4):
    """
    Given a snappy manifold M, assumed cusped and enhanced,
    calculate the set of exceptional fillings. Install the
    known exceptional slopes as M.slopes_non_hyp and the
    unidentified slopes as M.slopes_bad. Update the table
    M.exceptions_table if possible.
    """

    six_short_slopes = gt.find_short_slopes(M, six_theorem_length, normalized=False, verbose=verbose)
    for s in six_short_slopes:
        hyp_type = is_hyperbolic_filling(M, s, tries, verbose)
        if hyp_type == True:
            # We will deal with hyperbolic slopes later
            continue
        if hyp_type == False:
            M.slopes_non_hyp.add(s)
        if hyp_type == None: 
            M.slopes_bad.add(s)

    M.slopes_exclude = M.slopes_non_hyp.union(M.slopes_bad)
    # These are all the slopes excluded from hyperbolic methods
    
    verbose_print(verbose, 4, [M.name(), 'cusp_stuff', 'merid', M.mer_hol, 'long', M.long_hol])
    verbose_print(verbose, 5, ['cusp_stuff', 'norm_fac', M.norm_fac, 'homolog. long.', M.l_hom, 'homolog. merid.', M.m_hom])

    verbose_print(verbose, 3, [M.name(), len(M.slopes_non_hyp), 'non-hyperbolic slopes and', len(M.slopes_bad), 'bad slopes'])
    verbose_print(verbose, 5, [M.name(), 'non-hyp slopes', M.slopes_non_hyp])
    if len(M.slopes_bad) > 0:
        verbose_print(verbose, 0, [M.name(), 'bad slopes', M.slopes_bad])
        
    return None


def find_systole_short_slopes(M, tries=8, verbose=4):
    """
    Given a snappy manifold M, assumed cusped and enhanced,
    compute the systole of M and calculate the set of systole-short 
    hyperbolic fillings. Filter that set by homology, and
    install it as M.slopes_hyp.
    """

    M.sys = gt.systole_with_tries(M, tries=tries, verbose=verbose)
    verbose_print(verbose, 3, [M.name(), 'systole is at least', M.sys])
    if M.sys == None:
        return [(M.name(), None, None, None, 'systole fail')]
    
    norm_len_cutoff = max(9.97, sqrt((2*pi/M.sys) + 56.0).n(200)) 
    short_slopes = gt.find_short_slopes(M, norm_len_cutoff, normalized=True, verbose=verbose)
    verbose_print(verbose, 4, [M.name(), 'norm_len_cutoff', norm_len_cutoff])
    verbose_print(verbose, 3, [M.name(), len(short_slopes), 'short slopes found'])
    verbose_print(verbose, 5, short_slopes)
               
    M.slopes_hyp = {}
    for s in short_slopes:
        Q = M.copy()
        Q.dehn_fill(s)
        hom_hash = str(Q.homology())
        
        if s in M.slopes_exclude:
            verbose_print(verbose, 8, [M.name(), s, 'known exceptional or unidentified slope'])
            continue

        assert is_hyperbolic_filling(M, s, tries, verbose)
        # All slopes shorter than 6.01 should have been identified already. The new ones are hyperbolic.
        add_to_dict_of_sets(M.slopes_hyp, hom_hash, s)
            
    num_hyp_slopes = sum(len(M.slopes_hyp[hash]) for hash in M.slopes_hyp)
    verbose_print(verbose, 3, [M.name(), num_hyp_slopes, 'hyperbolic slopes'])
    verbose_print(verbose, 4, [M.name(), len(M.slopes_hyp), 'homology buckets of hyperbolic slopes'])
    verbose_print(verbose, 5, [M.name(), 'hyp slopes', M.slopes_hyp])

    return None


def find_low_volume_slopes(M, point, hom_gp, vol_max, tries, verbose):
    """
    Start with a manifold M, assumed one-cusped and enhanced.
    Consider the line in Dehn surgery space through a point (called "point")
    that is parallel to l_hom, the homological longitude. On this line, find 
    all slopes that satisfy:
    * not in the set M.slopes_exclude (hence hyperbolic)
    * have H_1(M(t)) isomorphic to hom_gp
    * have volume at most vol_max
    
    Return the set of these slopes.
    """
    
    cusped_vol = fetch_volume(M, (0,0), tries, verbose)
    l_max = HK_vol_bound_inv(cusped_vol - vol_max) * M.norm_fac  # length on cusp
    
    verbose_print(verbose, 12, ["Entering find_low_volume_slopes"])
    # name = M.name()
    low_vol_slopes = set()
    len_l_hom = abs(M.l_hom[0]*M.mer_hol + M.l_hom[1]*M.long_hol)
    
    # Find an interval on a line in Dehn surgery space that must contain
    # all comparison slopes that potentially have low enough volume.
    middle = gt.a_shortest_lattice_point_on_line(point, M.l_hom, M.mer_hol, M.long_hol)
    lower = int( (-l_max / len_l_hom).floor().lower() )
    upper = int( (l_max / len_l_hom).ceil().upper() )
    verbose_print(verbose, 25, ['lower, upper', lower, upper])
    
    # Now, scan the interval to determine low-volume comparison slopes
    for k in range(lower, upper + 1):
        verbose_print(verbose, 25, ['k', k])
        # move along the line 
        a = middle[0] + k * M.l_hom[0] 
        b = middle[1] + k * M.l_hom[1]
        t = gt.preferred_rep((a, b))
        a, b = t
        verbose_print(verbose, 25, ['t', t])
        if gcd(a, b) > 1:
            verbose_print(verbose, 25, [M.name(), hom_gp, k, t, 'excluded because gcd'])
            continue
        Q = M.copy()
        Q.dehn_fill(t)
        hom_gp_t = str(Q.homology())
        if hom_gp_t != hom_gp:
            verbose_print(verbose, 25, [M.name(), hom_gp, k, t, 'excluded because wrong homology'])
            continue
        if t in M.slopes_exclude:
            verbose_print(verbose, 25, [M.name(), hom_gp, k, t, 'excluded because non-hyperbolic or bad'])
            continue
        # Thus t is a hyperbolic filling, so 
        # First, check length
        verbose_print(verbose, 25, ['lengths', abs(a*M.mer_hol + b*M.long_hol), l_max])
        if abs(a*M.mer_hol + b*M.long_hol) <= l_max:
            # Then, check the volume
            t_vol = fetch_volume(M, t, tries, verbose)
            verbose_print(verbose, 25, ['t_vol', t_vol])
            verbose_print(verbose, 25, ['max_vol', vol_max])
            if not t_vol > vol_max:   # We need the 'not' because we are comparing intervals
                low_vol_slopes.add(t)
                verbose_print(verbose, 25, ['added to slopes_low_volume'])

    return low_vol_slopes



# Names - parsing regina names


def is_lens_space_from_name(name, verbose=3):
    """
    Given a regina name, parses it enough to decide if it is a lens
    space and then extracts the coefficients.  
    
    For our purposes, S2 x S1 is treated as a non-lens space.
    """

    verbose_print(verbose, 12, ["Entering is_lens_space_from_name"])
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
        # so give up
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
    # homework - check that regina sorts the coefficients.

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
        # so give up
        return False 

    if len(coeffs_0) != len(coeffs_1):
        verbose_print(verbose, 10, [name_0, name_1, "different number of singular fibers"])
        return True

    cone_pts_0 = [p for (p, q) in coeffs_0]
    cone_pts_1 = [p for (p, q) in coeffs_1]
    # homework - check that regina sorts the coefficients.

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

# Math

    
def product(nums):
    prod = 1
    for d in nums:
        prod = prod * d
    return prod


# Volume differences under filling


# we will need the following (compare Section 3.5 of Cosmetic computation paper)

# eccen = 3.3957
# u(z) = (eccen/2) * (z**2 * (z**4 + 4*z**2 - 1)) / (z**2 + 1)**3
# v(z) = (eccen/4) * ( (-2*z**5 + z**4 - z**3 + 2*z**2 - z + 1)/(z**2+1)**2 + arctan(z) - arctan(1.0) )
# v(z) is the integral of u from z to 1.
# Theorem 3.11 says: diff_vol < v(1 - (14.77)/L**2)

def HK_vol_bound(L):
    """
    Given a normalised length L (which is at least 9.93), returns an
    upper bound on the change of volume when filling a slope of that
    normalised length. 
    Reference: Hodgson-Kerckhoff 'Shape of DS space', Thm 5.12.
    Reference: our Theorem 3.11, which is a secant line approx to the above.
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
    
    We assume diff_vol > 0; otherwise this function cannot help.
    """
    
    if not diff_vol > 0:
        print("HK_vol_bound_inv error: need positive difference in volumes")
        raise
    
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


def are_distinguished_by_homology(M, s, N, t, verbose=5):
    """
    Given two parent manifolds M and N (assumed to be one-cusped) 
    and slopes s and t, decide whether M(s) and N(t) have distinct
    homology groups
    """
    
    verbose_print(verbose, 12, [M, s, N, t, "entering are_distinguished_by_homology"])
    Ms = M.copy()
    Nt = N.copy()
    Ms.dehn_fill(s)
    Nt.dehn_fill(t)
    
    Ms_hom = Ms.homology()
    Nt_hom = Nt.homology()
    verbose_print(verbose, 10, [Ms, str(Ms_hom)])
    verbose_print(verbose, 10, [Nt, str(Nt_hom)])
    
    return Ms_hom != Nt_hom



# Tests using covers

def subgroup_abels(G, deg):
    """
    Given a Gap group g, computes the list of finite-index subgroups up
    to index deg. Returns the list of subgroups, their indices, and their
    abelianizations (sorted lesicographically for comparing).
    """    
    
    subs = G.LowIndexSubgroupsFpGroup(deg)
    out = [[G.Index(H), H.AbelianInvariants()] for H in subs]
    out.sort()  # Sort lexicographically
    return subs, out
    

def profinite_data(G, subs):
    """
    Given a Gap group G, and a list of finite-index subgroups subs
    (presumed to be all subgroups up to some index), computes
    the following data for every subgroup H in subs:
    the index, the abelianization, the index of the normal core, 
    and the abelianization of the normal core.
    Returns the set of these invariants, sorted lexicographically.
    """

    out = []
    for H in subs:
        K = G.FactorCosetAction(H).Kernel()
        out.append([G.Index(H), H.AbelianInvariants(), G.Index(K), K.AbelianInvariants()])
    out.sort()
    return out


def are_distinguished_by_cover_homology(M, N, tries, verbose):
    """
    Given snappy manifolds M and N, tries to distinguish their
    fundamental groups using finite-index subgroups and their normal cores.
    """
    
    # verbose_print(verbose, 0, ['Foo!'])

    verbose_print(verbose, 12, [M, N, "entering are_distinguished_by_cover_homology"])
    
    GM = gap(M.fundamental_group().gap_string())
    GN = gap(N.fundamental_group().gap_string())
    degree_bound = min(tries, 6) # Hack: no degrees higher than 6
    
    # First, compute small-degree covers and their homology
    M_subs, M_data = subgroup_abels(GM, degree_bound)
    N_subs, N_data = subgroup_abels(GN, degree_bound)
    verbose_print(verbose, 8, [M, M_data])
    verbose_print(verbose, 8, [N, N_data])
    if M_data != N_data:
        verbose_print(verbose, 6, [M, N, "cover homology distinguishes"])
        return True
    
    # Next, try harder. Compute homology of normal cores.    
    M_invts = profinite_data(GM, M_subs)
    N_invts = profinite_data(GN, N_subs)
    verbose_print(verbose, 8, [M, M_invts])
    verbose_print(verbose, 8, [N, N_invts])
    if M_invts != N_invts:
        verbose_print(verbose, 6, [M, N, "homology of normal cores distinguishes"])
        return True
    else:
        verbose_print(verbose, 6, [M, N, "cover homology fails to distinguish"])
        return False


def are_distinguished_by_covers(M, s, N, t, tries, verbose):
    """
    Given snappy manifolds M and N, and a pair of slopes s and t, builds
    M(s) and N(t), computes a collection of covers of each, counts
    them, and returns True if the "spectrum" distinguishes.  If this
    fails, returns False.
    """
    
    verbose_print(verbose, 12, [M, s, N, t, "entering are_distinguished_by_covers"])
    Ms = M.copy()
    Nt = N.copy()
    Ms.dehn_fill(s)
    Nt.dehn_fill(t)
    return are_distinguished_by_cover_homology(Ms, Nt, tries, verbose)




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


def fetch_exceptional_data(M, s, field, tries = 3, verbose = 2):
    """
    Given a manifold M (assumed to be one-cusped and enhanced via enhance_manifold), 
    we wish to update M.exceptions_table.  This is a database where the
    keys are slopes (here s).  The fields are useful data about
    exceptional fillings that we don't want to compute twice.  Remark:
    If we fail to compute an invariant, we don't install anything in
    the table and just return None.
    """
    # convention - no empty fields - aka no placeholders. 

    verbose_print(verbose, 12, [M, s, "entering exceptions table", field])
    
    allowed_fields = ["fund_gp", "name", "atoroidal_sfs", "reducible", "toroidal"]
    # The field "lens" used to be allowed, but it is no more.
    assert field in allowed_fields
    
    if not s in M.exceptions_table:
        M.exceptions_table[s] = {}

    if field in M.exceptions_table[s]:
        verbose_print(verbose, 10, [M, s, field, 'found in table'])
        return M.exceptions_table[s][field]
    
    # We did not find the field, so we have to install and return it.

    N = M.copy()
    N.dehn_fill(s)
    
    if field == "fund_gp":
        out = fundamental.is_exceptional_due_to_fundamental_group(N, tries, verbose)
        is_except, _ = out
        if is_except:
            M.exceptions_table[s]["fund_gp"] = out
        return out
    
    if field == "name":
        try:
            name = dunfield.regina_name(N)
        except:
            print(N)
            raise
        if name != None:
            M.exceptions_table[s]["name"] = name
            verbose_print(verbose, 10, [N, name, 'added to table'])
            return name
        else:
            # try to see if N is a toroidal mixed manifold
            is_tor, pieces = fetch_exceptional_data(M, s, "toroidal", tries, verbose)
            if is_tor:
                # Convert the list of JSJ pieces into a pseudo-name
                piece_names = [p[1] for p in pieces]
                name = ' U/? '.join(sorted(piece_names))
                M.exceptions_table[s]["name"] = name
                verbose_print(verbose, 10, [N, name, 'pseudo-name added to table'])
                return name
            else:
                verbose_print(verbose, -1, [N, "could not compute name"])
                return None
    
    if field == "atoroidal_sfs":
        name = fetch_exceptional_data(M, s, "name", tries, verbose)
        if name == None:
            return (None, None)

        out = is_closed_sfs_from_name(name)
        is_sfs, geom, base, coeffs = out
        if is_sfs and geom in ["Lens", "Elliptic", "S2 x R"]:
            M.exceptions_table[s]["atoroidal_sfs"] = out
            verbose_print(verbose, 10, [N, name, 'Atoroidal sfs coeffs added to table'])
            return out
        elif is_sfs and base == "S2" and (len(coeffs) <= 3):
            M.exceptions_table[s]["atoroidal_sfs"] = out
            verbose_print(verbose, 10, [N, name, 'Atoroidal sfs coeffs added to table'])
            return out        
        else:
            verbose_print(verbose, 10, [N, s, name, "Not recognized as atoroidal SFS"])
            return (None, geom, base, coeffs)
        
    if field == "reducible":
        out = gt.is_reducible_wrapper(N, tries, verbose)
        M.exceptions_table[s]["reducible"] = out
        verbose_print(verbose, 10, [N, out, 'reducibility'])
        return out
        
    if field == "toroidal":
        out = gt.torus_decomp_wrapper(N, tries, verbose)
        M.exceptions_table[s]["toroidal"] = out
        verbose_print(verbose, 10, [N, out, 'toroidality'])
        return out
        
        
def fetch_volume(M, s, tries, verbose):
    """
    Given a manifold M (assumed to be one-cusped , enhanced, and 
    equipped with a good triangulation) and a slope s (assumed to be 
    hyperbolic), fetch the volume. This means: pull the volume from the 
    table if it is there; else, try to compute it, and then store in the 
    table. Return the volume either way.
    """
    verbose_print(verbose, 12, [M, s, "entering fetch_volume"])

    if s in M.volumes_table:
        verbose_print(verbose, 10, [M, s, 'volume found in table'])
        return M.volumes_table[s]
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
            M.volumes_table[s] = R(N.volume())
        else: 
            M.volumes_table[s] = vol

    return M.volumes_table[s]
        


def is_hyperbolic_filling(M, s, tries, verbose):
    """
    Given a one-cusped manifold M (assumed hyperbolic and enhanced) and a slope s,
    try to determine if M(s) is hyperbolic or exceptional.  Returns
    True or False respectively, and returns None if we failed.
    """
    
    # TODO: Check for Regina name earlier in the logic!!!
    
    verbose_print(verbose, 12, [M, s, 'entering is_hyperbolic_filling'])
    p, q = s
    # We don't recompute cusp_invariants because it is slow
    # m, l, _ = cusp_invariants(C)
    if abs(p*M.mer_hol + q*M.long_hol) > 6: # six-theorem
        verbose_print(verbose, 10, [M, s, 'has length', abs(p*M.mer_hol + q*M.long_hol), 'hence the filling is hyperbolic by 6-theorem'])
        return True            

    N = M.copy()
    N.dehn_fill(s)

    for i in range(tries):

        for j in range(i + 1):
            N.randomize()  # Note: the randomized triangulation will stay with us until the next i
            is_except, _ = fetch_exceptional_data(M, s, "fund_gp", tries, verbose)
            if is_except:
                return False
            
        for j in range(1): # this is not a typo.  :P
            if dunfield.is_hyperbolic(N, 2*i + 1, verbose): # because Nathan randomises for us.
                # at this moment we trust the volume so put it in the table?
                return True
            
        if i == 0: # this is trustworthy and expensive.
            # Check reducibility and maybe small SFS here, to prevent code from spinning its wheels
            is_tor, _ = fetch_exceptional_data(M, s, "toroidal", tries, verbose)
            if is_tor: 
                return False
            
    # ok, nothing "easy" worked

    name = fetch_exceptional_data(M, s, "name", tries, verbose)
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



def are_distinguished_exceptionals(M, s, N, t, tries=8, verbose=5):
    """
    Given a one-cusped manifolds M and N, equipped with slopes s and t,
    (where we think that both M(s), N(t) are non-hyperbolic), try to  
    distinguish the fillings. Invariants that we check include (in order):
    1) Homology
    2) Regina names and Seifert invariants
    2) Irreducibility (via Regina)
    3) Toroidality (via Regina)
    4) Number of covers of small degree
    """
    
    verbose_print(verbose, 12, [M, s, N, t, 'entering are_distinguished_exceptionals'])

    if are_distinguished_by_homology(M, s, N, t, verbose=verbose):
        return True

    s_name = fetch_exceptional_data(M, s, "name", tries, verbose)
    t_name = fetch_exceptional_data(N, t, "name", tries, verbose)

    verbose_print(verbose, 10, ["comparing", s_name, "to", t_name])

    # Rapid tests that require only s_name and t_name     
    if s_name == t_name:
        # We have no hope of distinguishing this pair.
        return False
    
    if are_distinguished_closed_sfs(s_name, t_name, verbose):
        return True
    if are_distinguished_graph_pairs(s_name, t_name, verbose):
        return True
     
    s_ator_sfs, s_geom, _, _ = fetch_exceptional_data(M, s, "atoroidal_sfs", tries, verbose)
    t_ator_sfs, t_geom, _, _ = fetch_exceptional_data(N, t, "atoroidal_sfs", tries, verbose)

    # Less rapid tests, which require the name of one manifold and normal surface theory on the other.

    if s_ator_sfs:
        t_red, _ = fetch_exceptional_data(N, t, "reducible", tries, verbose)
        if s_geom != "S2 x R" and t_red:
            # M(s) is irreducible but M(t) is reducible
            verbose_print(verbose, 6, [s_name, t_name, "only one is reducible"])
            return True
        t_tor, _ = fetch_exceptional_data(N, t, "toroidal", tries, verbose)
        if t_tor:
            # M(s) is atoroidal but M(t) is toroidal
            verbose_print(verbose, 6, [s_name, t_name, "only one is toroidal"])
            return True                    
    if t_ator_sfs:
        s_red, _ = fetch_exceptional_data(M, s, "reducible", tries, verbose)
        if t_geom != "S2 x R" and s_red:
            # M(t) is irreducible but M(s) is reducible
            verbose_print(verbose, 6, [s_name, t_name, "only one is reducible"])
            return True                    
        s_tor, _ = fetch_exceptional_data(M, s, "toroidal", tries, verbose)
        if s_tor:
            # M(t) is atoroidal but M(s) is toroidal
            verbose_print(verbose, 6, [s_name, t_name, "only one is toroidal"])
            return True
    
    # At this point, both manifolds should be reducible, or both toroidal (or we have failed to identify a SFS).    
    # We should probably compare reducible manifolds using their prime decompositions.

    # Tests that search for covers are pretty slow, but effective.                    
    if are_distinguished_by_covers(M, s, N, t, tries, verbose):
        return True
    
    return False        


def are_isometric_fillings(M, s, N, t, tries=8, verbose=4):
    """
    Given cusped manifolds M and N, and slopes s and t, try to prove that
    M(s) is isometric to N(t).
    
    Return True if successful, or None otherwise
    """
    
    Q = M.copy()
    Q.dehn_fill(s)
    R = N.copy()
    R.dehn_fill(t)
    
    for i in range(tries):
        for j in range(i):
            isisom = False
            try: 
                isisom = Q.is_isometric_to(R)
            except:
                verbose_print(verbose, 2, [Q, R, 'isometry checker crashed'])
            if isisom:
                verbose_print(verbose, 8, [Q, 'proved isometric to', R, 'on try', (i,j)])
                return True
            R.randomize()
        Q.randomize()
    
    return None


# finding common fillings of M and N

def find_common_hyp_fillings(M, N, tries, verbose):
    """
    Given one-cusped, enhanced manifolds M and N, compare every systole-short
    Dehn filling of M to the appropriate volume-short set of fillings of N.
    Find and return the ones that *might* produce the same 3-manifold.
    
    Warning: This routine is asymmetric in M and N.
    """
    
    # Initialization for M
    find_systole_short_slopes(M, tries, verbose)    

    # Initialization for N. This includes homologies of meridional and longitudinal fillings.

    N_vol = fetch_volume(N, (0,0), tries, verbose)
    Q = N.copy()
    Q.dehn_fill(N.m_hom)
    N_mer_base = order_of_torsion(Q) # Every non-longitudinal filling of N will have torsion homology some multiple of this order.
    Q.dehn_fill(N.l_hom)
    N_long_homology = str(Q.homology())
    N_long_order = order_of_torsion(Q)
    verbose_print(verbose, 12, [N.name(), 'meridional homology', N_mer_base, 'longitudinal homology', N_long_order])

    # Searching through homology hashes for M 
    common_uns = []
    for hom_hash in M.slopes_hyp:
        s0 = list(M.slopes_hyp[hom_hash])[0]    # a representative slope 
        Q = M.copy()
        Q.dehn_fill(s0)
        tor_order = order_of_torsion(Q)
        verbose_print(verbose, 12, [M.name(), hom_hash, tor_order])
        hom_gp = hom_hash
        if (hom_hash != N_long_homology) and (tor_order % N_mer_base != 0):
            verbose_print(verbose, 12, [M.name(), hom_hash, 'cannot have common fillings with', N.name(), 'for homological reasons'])
            continue

        if hom_hash == N_long_homology and N.l_hom not in N.slopes_exclude:
            verbose_print(verbose, 12, ['Need to compare M fillings to hyperbolic longitudinal filling of N'])
            t = N.l_hom
            N_t_vol = fetch_volume(N, t, tries, verbose)
            for s in M.slopes_hyp[hom_hash]:
                M_s_vol = fetch_volume(M, s, tries, verbose)
                verbose_print(verbose, 12, [M.name(), s, M_s_vol, N.name(), t, N_t_vol, 'volumes'])
                if M_s_vol > N_t_vol or N_t_vol > M_s_vol:
                    verbose_print(verbose, 12, [M.name(), s, N.name(), t, 'verified volume distinguishes'])
                    continue
                if are_distinguished_by_covers(M, s, N, t, tries, verbose):
                    verbose_print(verbose, 6, [M.name(), s, N.name(), t, 'cover spectrum distinguishes'])
                    continue
                
                reason = (M.name(), s, N.name(), t, M_s_vol, N_t_vol)
                verbose_print(verbose, 2, [reason])
                common_uns.append(reason)
                    
        # Compare each fillings M(s) for s in M.slopes_hyp[hom_hash] to a set of fillings of N.
        # Every member of this set should have intersection number p with N.l_hom.
        p = int(tor_order / N_mer_base)  # This will be an integer once we've landed here
        point = (p*N.m_hom[0], p*N.m_hom[1])
        verbose_print(verbose, 25, ['p', p])
        verbose_print(verbose, 25, ['point on Dehn surgery line', point])
        for s in M.slopes_hyp[hom_hash]:
            # find coords of slope s in original framing
            s_orig = gt.preferred_rep((gt.alg_int(s, M.longitude), gt.alg_int(M.meridian, s))) 
            M_s_vol = fetch_volume(M, s, tries, verbose)
            if M_s_vol > N_vol:
                verbose_print(verbose, 12, [M, s, M_s_vol, 'volume too high for common fillings with', N, N_vol])
                continue
            if not M_s_vol < N_vol:
                reason = (M.name(), s_orig, N.name(), None, M_s_vol, N_vol)
                common_uns.append(reason)
                verbose_print(verbose, 12, [M, s, M_s_vol, 'cannot distinguish volume from', N, N_vol])
                continue
            # At this point, we have M_s_vol < N_vol
            N_low_vol_slopes = find_low_volume_slopes(N, point, hom_gp, M_s_vol, tries, verbose)
            if len(N_low_vol_slopes) > 0:
                verbose_print(verbose, 6, [M.name(), s, hom_hash, N.name(), N_low_vol_slopes, 'low volume slopes'])
            for t in N_low_vol_slopes:
                N_t_vol = fetch_volume(N, t, tries, verbose)
                if M_s_vol > N_t_vol or M_s_vol < N_t_vol:
                    verbose_print(verbose, 6, [M.name(), s, N.name(), t, 'verified volume distinguishes'])
                    continue
                if are_distinguished_by_covers(M, s, N, t, tries, verbose):
                    verbose_print(verbose, 6, [M.name(), s, N.name(), t, 'cover spectrum distinguishes'])
                    continue

                # find coordinates of t in original framings
                t_orig = gt.preferred_rep((gt.alg_int(t, N.longitude), gt.alg_int(N.meridian, t)))
                
                # Now that we have tried and failed to distinguish, try to prove tha they are the same
                if are_isometric_fillings(M, s, N, t, tries, verbose):
                    reason = (M.name(), s_orig, N.name(), t_orig, M_s_vol, 'isometric')
                else:
                    reason = (M.name(), s_orig, N.name(), t_orig, M_s_vol, 'cannot distinguish')
                verbose_print(verbose, 2, [reason])
                common_uns.append(reason)

    return common_uns


def find_common_fillings(M, N, ExcludeS3 = False, tries=8, verbose=4):
    """
    Given one-cusped manifolds M and N, we search for common Dehn fillings,
    that is, pairs of slopes s,t such that M(s) might be homeomorphic to N(t).
    
    Return a list of tuples - (M, s, N, t, 'reason') where M(s) and N(t)
    are possibly the same manifold. The output should contain the list of
    potential pairs, but might have some fluff (non-distinguished pairs).
    
    If check_chiral==False, then we only check for orientation-preserving
    homeos.

    If check_chiral==True, then we check for both orientation-preserving
    and orientation-reversing homeos.
    
    This routine is designed for the situation when M != N. If M == N, use 
    check_cosmetic instead.
    
    At the moment (2023-02-28), the code has an asymmetry between M and N.
    So it needs to be run twice, interchanging M <--> N the second time.
    """

    verbose_print(verbose, 12, [M, N, "entering find_common_fillings"])
    
    # Let's be liberal in accepting 'M' as either a name or manifold class
    M = snappy.Manifold(M)
    N = snappy.Manifold(N)
    
    # but not too liberal!

    if not M.num_cusps() == 1:
        return [(M.name(), None, None, None, 'wrong number of cusps')]
    if not N.num_cusps() == 1:
        return [(N.name(), None, None, None, 'wrong number of cusps')]

    # Install good hyperbolic metrics on M or N. Give up if we cannot find such a metric.
        
    mfd, reason = gt.sanity_check_cusped(M, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure, so give up.
        return [(M.name(), None, None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        M = mfd

    mfd, reason = gt.sanity_check_cusped(N, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure, so give up.
        return [(N.name(), None, None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        N = mfd

    if M.is_isometric_to(N):
        # All their Dehn fillings will coincide
        verbose_print(verbose, 3, [M.name(), N.name(), 'are isometric'])    
        return [(M.name(), None, N.name(), None, 'isometric parent manifolds')]


    # Step one - compute the list of exceptional fillings of both M and N.

    enhance_manifold(M, tries, verbose)  
    find_exceptionals(M, tries, verbose)
        
    enhance_manifold(N, tries, verbose)  
    find_exceptionals(N, tries, verbose)
    
    # TODO: remember the initial framings of M and N that we were handed, and 
    # report shared fillings in initial framing.


    # Step two: check for (non-hyperbolic) homeomorphic pairs in 
    # M.slopes_non_hyp and N.slopes_non_hyp.
    # Note that slopes_bad automatically gets recorded and reported.

    bad_uns = []
    for s in M.slopes_bad:
        reason = (M.name(), s, None, None, 'Could not verify hyperbolicity')
        verbose_print(verbose, 2, [reason])
        bad_uns.append(reason)
    for t in N.slopes_bad:
        reason = (N.name(), t, None, None, 'Could not verify hyperbolicity')
        verbose_print(verbose, 2, [reason])
        bad_uns.append(reason)


    for s in M.slopes_non_hyp:
        for t in N.slopes_non_hyp:

            verbose_print(verbose, 7, ["Comparing", M.name(), s, "to", N.name(), t])

            # Most of the work is now in this routine
            if are_distinguished_exceptionals(M, s, N, t, tries=tries, verbose=verbose):
                continue

            # find coordinates of s and t in original framings
            s_orig = gt.preferred_rep((gt.alg_int(s, M.longitude), gt.alg_int(M.meridian, s)))
            t_orig = gt.preferred_rep((gt.alg_int(t, N.longitude), gt.alg_int(N.meridian, t)))
            
            s_name = fetch_exceptional_data(M, s, "name", tries, verbose)
            t_name = fetch_exceptional_data(N, t, "name", tries, verbose)

            reason = (M.name(), s_orig, N.name(), t_orig, s_name, t_name)
            if ExcludeS3 and s_name == 'S3' and t_name == 'S3':
                verbose_print(verbose, 2, ['Excluding', reason])
                continue

            verbose_print(verbose, 2, [reason])
            bad_uns.append(reason)


    # Step four - Compare the volume-short fillings of M to the systole-short fillings of N.
    # Then, do the reverse.


    commons_M_first = find_common_hyp_fillings(M, N, tries, verbose)
    commons_N_first = find_common_hyp_fillings(N, M, tries, verbose)
    
    commons_N_converted = [(line[2], line[3], line[0], line[1], line[4], line[5]) for line in commons_N_first]
    # Reorder the output of commons_N_first to put M back in the first spot


    # Step five - Remove duplicates. This is not done yet.
    
    bad_uns.extend(commons_M_first)    
    
    # Add the lines of commons_N_converted one at a time, checking for duplicates
    
    for N_line in commons_N_converted:
        found = False
        for j in range(len(bad_uns)):
            M_line = bad_uns[j]
            if M_line[:4] == N_line[:4]: # same pair of slopes
                found = True
                verbose_print(verbose, 12, ['duplicate entry', N_line])
                if N_line[5] == 'isometric':
                    # Keep the version that provides more certainty
                    bad_uns[j] = N_line
        if found == False:
            verbose_print(verbose, 12, ['adding entry', N_line])
            bad_uns.append(N_line)

    
    verbose_print(verbose, 5, [M.name(), N.name(), 'non-distinguished pairs', bad_uns])
    
    return bad_uns


def check_cosmetic(M, use_BoyerLines=True, check_chiral=False, tries=8, verbose=4):
    """
    Given a one-cusped manifold M we equip it with a shortest framing
    and then return a list of tuples - (name, s, t, 'reason') where s
    and t are possibly a cosmetic pair.
    
    If use_BoyerLines==True, then we apply the Boyer-Lines theorem:
    the Casson invariant obstructs purely cosmetic surgeries.
    
    If check_chiral==False, then we only check for purely cosmetic 
    surgeries. 

    If check_chiral==True, then we check for chirally cosmetic surgeries
    as well as purely cosmetic ones. 
    """

    verbose_print(verbose, 12, [M, "entering check_cosmetic"])
    
    # Let's be liberal in what we accept
    M = snappy.Manifold(M)

    # but not too liberal!
    if not M.num_cusps() == 1:
        return [(M.name(), None, None, 'wrong number of cusps')]
        
    # If H_1(M) = Z, we can apply the Boyer-Lines criterion to rule out cosmetic surgeries

    if use_BoyerLines and not check_chiral:
        h = M.homology()
        if h.betti_number() == 1 and h.rank() == 1:
            # M is the complement of a knot in an integer homology sphere
            if Casson_invt(M, verbose) != 0:
                # The second derivative of the Alexander polynomial at 1 is nonzero,
                # so M has no cosmetic surgeries by Boyer-Lines
                verbose_print(verbose, 2, [M.name(), 'has no cosmetic surgeries by Boyer-Lines'])
                return []

    # From now on, we need geometry. Install a good hyperbolic metric,
    # or give up if we cannot find one.
    
    mfd, reason = gt.sanity_check_cusped(M, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure, so give up.
        return [(M.name(), None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        M = mfd

    # Step one: identify exceptional fillings.
            
    enhance_manifold(M, tries, verbose)  
    find_exceptionals(M, tries, verbose)

    
    # Step two: check for (non-hyperbolic) cosmetic pairs in slopes_non_hyp.
    # Note that slopes_bad automatically gets recorded and reported.

    bad_uns = []  # Pairs of potentially cosmetic slopes
    for s in M.slopes_bad:
        reason = (M.name(), None, s, 'Could not verify hyperbolicity')
        verbose_print(verbose, 2, [reason])
        bad_uns.append(reason)

    for s in M.slopes_non_hyp:
        for t in M.slopes_non_hyp:
            if t < s:
                # We will have checked the pair (t, s) separately.
                continue 
            if gt.alg_int(s, t) == 0:
                # Parallel slopes cannot be cosmetic.
                continue

            verbose_print(verbose, 7, [M.name(), "comparing filling", s, "to", t])

            # Most of the work is now in this routine
            if are_distinguished_exceptionals(M, s, M, t, tries=tries, verbose=verbose):
                continue

            s_name = fetch_exceptional_data(M, s, "name", tries, verbose)
            t_name = fetch_exceptional_data(M, t, "name", tries, verbose)

            reason = (M.name(), s, t, s_name, t_name)

            # Try a couple more tests using Gordon-Luecke and CGLS using s_name and t_name     

            if "#" in s_name and "#" in t_name:
                if abs(gt.alg_int(s,t)) > 1:
                    # Gordon and Luecke proved distance between reducible fillings must be 1.
                    verbose_print(verbose, 2, [s_name, t_name, "distinguished by Gordon-Luecke theorem on distance between reducible fillings"])
                    continue
            s_lens, _ = is_lens_space_from_name(s_name, verbose)
            t_lens, _ = is_lens_space_from_name(t_name, verbose)
            if s_name == "S2 x S1" or s_lens or t_name == "S2 x S1" or t_lens:
                if abs(gt.alg_int(s,t)) > 1:
                    # Cyclic surgery theorem
                    verbose_print(verbose, 2, [s_name, t_name, "distinguished by cyclic surgery theorem"])
                    continue
            
            verbose_print(verbose, 2, [reason])
            bad_uns.append(reason)
    

    # Step three: Get the systole of M. Find the systole-short hyperbolic slopes,
    # and split them by homology.
    
    find_systole_short_slopes(M, tries, verbose)


    # Step four - Compute the max of the volumes in
    # M.slopes_hyp[hom_hash] and use this to compute the larger set of
    # "comparison slopes".

    max_volumes = {}
    for hom_hash in M.slopes_hyp:
        max_volumes[hom_hash] = max(fetch_volume(M, s, tries, verbose) for s in M.slopes_hyp[hom_hash])

    verbose_print(verbose, 5, [M.name(), 'max volumes by homology', max_volumes])

    slopes_low_volume = {}
    for hom_hash in M.slopes_hyp:
        verbose_print(verbose, 25, ['slopes hyp', M.slopes_hyp[hom_hash]])
        vol_max = max_volumes[hom_hash]
        if verbose > 25:
            print('hom_hash, max_vol[hom_hash]', hom_hash, vol_max)
            print('l_max_normalized', HK_vol_bound_inv(M.volume() - vol_max))
            print('normalized length endpoints', (l_max/M.norm_fac).endpoints(),)
            print('norm_fac', M.norm_fac.endpoints())

        hom_gp = hom_hash
        s = list(M.slopes_hyp[hom_hash])[0]  # some representative slope
        p = abs(gt.alg_int(s, M.l_hom))
        verbose_print(verbose, 20, [M.name(), hom_hash, s, p])
        
        point = (p*M.m_hom[0], p*M.m_hom[1])
        out = find_low_volume_slopes(M, point, hom_gp, vol_max, tries, verbose)
        if len(out) > 0:      # This should never fail -- see next assert
            slopes_low_volume[hom_hash] = out
        
        # Sanity check: M.slopes_hyp[hom_hash] should be a subset of slopes_low_volume[hom_hash]
        for t in M.slopes_hyp[hom_hash]:
            assert t in slopes_low_volume[hom_hash]

    num_low_volume = sum(len(slopes_low_volume[hash]) for hash in slopes_low_volume)
    verbose_print(verbose, 3, [M.name(), num_low_volume, 'low volume slopes found'])
    verbose_print(verbose, 5, [M.name(), '(somewhat-)low volume slopes', slopes_low_volume])

    # Step five - check for hyperbolic cosmetic pairs.
    # That is: for all p, slopes s in M.slopes_hyp[hom_hash], and slopes t in
    # slopes_low_volume[hom_hash] (with s \neq t) show that M(s) is not
    # orientation-preservingly homeomorphic to M(t).  Collect
    # counterexamples and difficult cases to be returned to calling
    # function.

    for hom_hash in M.slopes_hyp:
        for s in M.slopes_hyp[hom_hash]:
            for t in slopes_low_volume[hom_hash]:
                if t in M.slopes_hyp[hom_hash] and t < s:
                    # since M.slopes_hyp[hom_hash] \subset slopes_low_volume[hom_hash],
                    # we will have also checked the pair (t, s) so skip!
                    continue 
                if gt.alg_int(s,t) == 0:
                    continue
                s_vol = fetch_volume(M, s, tries, verbose)
                t_vol = fetch_volume(M, t, tries, verbose)
                verbose_print(verbose, 12, [M, s, t, s_vol, t_vol, 'volumes'])
                if s_vol > t_vol or t_vol > s_vol:
                    verbose_print(verbose, 6, [M, s, t, 'verified volume distinguishes'])
                    continue
                looks_distinct, rigorous = False, False
                if not check_chiral:
                    # Try to distinguish by oriented hyperbolic invariants
                    looks_distinct, rigorous = gt.are_distinguished_by_hyp_invars(M, s, t, tries, verbose)
                    if looks_distinct and rigorous:
                        continue
                    
                if are_distinguished_by_covers(M, s, M, t, tries, verbose):
                    continue
                    
                if looks_distinct and not rigorous:
                    reason = (M.name(), s, t, 'distinguished by non-rigorous length spectrum')
                    # Temporary flag to make sure we never land here
                    verbose_print(verbose, 0, [M.name(), s, t, 'distinguished by non-rigorous length spectrum'])
                    raise
                if not looks_distinct:
                    reason = (M.name(), s, t, 'Not distinguished by hyperbolic invariants or covers')
                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)

    verbose_print(verbose, 1, [M.name(), 'non-distinguished pairs', bad_uns])
    
    return bad_uns
    

def check_list_for_common_fillings(M, manifolds, ExcludeS3 = False, tries=7, verbose=4, report=20):
    """
    Given a cusped SnapPy manifold M, and a list called 'manifolds', check for common
    Dehn fillings of M and one of the manifolds in the list.
    
    Returns a list of tuples containing the slopes that give (confirmed or suspected) common fillings.
    
    If the flag ExcludeS3 is set to True, then the user does not want common S3 fillings
    reported. This would be the case when searching a known list of knot complements.
    """
    
    verbose_print(verbose, 12, ["entering check_list_for_common_fillings"])
    
    M = snappy.Manifold(M)
    
    bad_uns = []
    for n, N in enumerate(manifolds):
        N = snappy.Manifold(N)
        new_uns = find_common_fillings(M, N, ExcludeS3=ExcludeS3, tries=tries, verbose=verbose)
        bad_uns.extend(new_uns)
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n])
            verbose_print(verbose, 0, [bad_uns])
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
        M = snappy.Manifold(M)
        name = M.name()
            
        uns = check_cosmetic(M, use_BoyerLines=use_BoyerLines, check_chiral=False, tries=tries, verbose=verbose)
        if len(uns) > 0:
            is_amph, cob = is_amphichiral(M, tries=tries, verbose=verbose)
            if is_amph:
                for line in uns:
                    s = line[1]
                    t = line[2]
                    filled_name = line[3]
                    if is_chiral_graph_mfd_from_name(filled_name) and gt.preferred_rep(cob*vector(s)) == t:
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
        M = snappy.Manifold(M)
        name = M.name()

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
        M = snappy.Manifold(M)
        name = M.name()

        sol_type = M.solution_type()
    
        if sol_type != 'all tetrahedra positively oriented' and sol_type != 'contains negatively oriented tetrahedra':
            verbose_print(verbose, 2, [M, 'bad solution type for unclear reasons.'])
            bad_uns.append((name, None, None, 'bad solution type for unclear reasons'))
            continue
            
        distinct = gt.are_distinguished_by_length_spectrum(M, s, t, check_chiral=True, cutoff = cutoff, verbose=verbose)
        if not distinct:
            verbose_print(verbose, 4, [M, s, t, 'not distinguished by length spectrum up to', cutoff])
            bad_uns.append((name, s, t, 'not distinguished by length spectrum up to '+str(cutoff) ))
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n])
            verbose_print(verbose, 0, [bad_uns])
    return bad_uns
           
            
