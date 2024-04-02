#
# cosmetic_mfds.py
#

# This program does the following top-level tasks:
# 1. Check a given one-cusped hyperbolic three-manifold for cosmetic
# fillings.
# 2. Check a given pair of cusped hyperbolic manifolds for common
# fillings.

# TODO: Add examples of usage.


# Imports 

import snappy
import regina
import dunfield
import geom_tests as gt
import regina_tests as rt
import fundamental as ft

from verbose import verbose_print

# from sage.rings.rational_field import QQ
from sage.functions.other import sqrt, ceil, floor
from sage.symbolic.constants import pi
from sage.arith.misc import gcd, xgcd, factor
from sage.functions.trig import arctan
from sage.rings.real_mpfi import RealIntervalFieldElement
from sage.rings.real_mpfi import RIF
from sage.rings.real_mpfi import RealIntervalField
from sage.misc.functional import det
from sage.modules.free_module_element import vector
# from sage.interfaces.gap import gap


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
    # Install shortest
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

def find_exceptionals(M, tries = 8, verbose = 4):
    """
    Given a snappy manifold M, assumed cusped and enhanced,
    calculate the set of exceptional fillings. Install the
    known exceptional slopes as M.slopes_non_hyp and the
    unidentified slopes as M.slopes_bad. Update the table
    M.exceptions_table if possible.
    """

    six_short_slopes = gt.find_short_slopes(M, verbose=verbose)
    m, l = M.mer_hol, M.long_hol
    for s in six_short_slopes:
        hyp_type = gt.is_hyperbolic_filling(M, s, m, l, tries, verbose)
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
    Takes as in input a snappy manifold M, assumed cusped and enhanced, 
    and equipped with M.slopes_exclude (a calculated set of exceptional fillings).
    Given such M, compute the systole of M and calculate the set of systole-short 
    hyperbolic fillings. Filter that set by homology, and
    install it as M.slopes_hyp.
    
    Returns True if everything works as expected, or None if the systole 
    computation fails. 
    """

    M.sys = gt.systole_with_tries(M, tries=tries, verbose=verbose)
    if M.sys == None:
        verbose_print(verbose, 0, [M.name(), 'systole fail!'])
        return None
    M.sys = 0.99 * M.sys # In lieu of verification, allow for numerical error
    verbose_print(verbose, 3, [M.name(), 'systole is at least', M.sys])
    
    norm_len_cutoff = max(9.97, sqrt((2*pi/M.sys) + 56.0).n(200)) 
    short_slopes = gt.find_short_slopes(M, norm_len_cutoff, normalized=True, verbose=verbose)
    verbose_print(verbose, 4, [M.name(), 'norm_len_cutoff', norm_len_cutoff])
    verbose_print(verbose, 3, [M.name(), len(short_slopes), 'short slopes found'])
    verbose_print(verbose, 5, short_slopes)
               
    M.slopes_hyp = {}
    m, l = M.mer_hol, M.long_hol
    for s in short_slopes:
        Q = M.copy()
        Q.dehn_fill(s)
        hom_hash = str(Q.homology())
        
        if s in M.slopes_exclude:
            verbose_print(verbose, 8, [M.name(), s, 'known exceptional or unidentified slope'])
            continue

        assert gt.is_hyperbolic_filling(M, s, m, l, tries, verbose)
        # All slopes not in M.slopes_exclude are necessarily hyperbolic.
        add_to_dict_of_sets(M.slopes_hyp, hom_hash, s)
            
    num_hyp_slopes = sum(len(M.slopes_hyp[hash]) for hash in M.slopes_hyp)
    verbose_print(verbose, 3, [M.name(), num_hyp_slopes, 'hyperbolic slopes'])
    verbose_print(verbose, 4, [M.name(), len(M.slopes_hyp), 'homology buckets of hyperbolic slopes'])
    verbose_print(verbose, 5, [M.name(), 'hyp slopes', M.slopes_hyp])

    return True


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


# Volume differences under filling


# we will need the following (compare Section 3.3 of Cosmetic computation paper)

# eccen = 3.3957
# u(z) = (eccen/2) * (z**2 * (z**4 + 4*z**2 - 1)) / (z**2 + 1)**3
# v(z) = (eccen/4) * ( (-2*z**5 + z**4 - z**3 + 2*z**2 - z + 1)/(z**2+1)**2 + arctan(z) - arctan(1.0) )
# v(z) is the integral of u from z to 1.
# Theorem 3.14 says: diff_vol < v(1 - (14.77)/L**2)


def HK_vol_bound(L):
    """
    Given a normalised length L (which is at least 9.93), returns an
    upper bound on the change of volume when filling a slope of that
    normalised length. 

    Reference: Hodgson-Kerckhoff 'Shape of DS space', Thm 5.12.
    Reference: Our Theorem 3.14, which is a secant line approx to the above.
    """
    assert L > RIF(9.93)
    z = 1 - (RIF(14.77))/L**2
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
        raise ArithmeticError("HK_vol_bound_inv error: need positive difference in volumes")
    
    L = RIF(9.95)  # the lowest length we can return
    
    if HK_vol_bound(L) <= diff_vol:
        return L
    while HK_vol_bound(L) > diff_vol:
        L = 2 * L
    L_up = L
    L_down = L/2
    while L_up - L_down > RIF(0.1)**(digits):
        L_mid = (L_up + L_down)/2
        if HK_vol_bound(L_mid) > diff_vol:
            L_down = L_mid
        else:
            L_up = L_mid
    return L_up
            

# Cusped manifolds with H_1(M) = Z can be ruled out via Boyer-Lines
# criterion on Casson invariant (second deriv of Alexander polynomial)


def Casson_invt(M, verbose = 3):
    """
    Given a one-cusped (snappy) manifold M, return the Casson invariant.

    Reference: Boyer-Lines "Surgery formulae for Casson's invariant..."
    """

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


# hyperbolic invariants


def is_amphichiral(M, tries = 8, verbose = 3):
    """
    Given an orientable hyperbolic cusped Snappy three-manifold,
    decides if it has an orientation reversing isometry.
    
    Returns a Boolean and (if amphichiral) an orientation-reversing
    change of basis matrix for the cusp.
    """
    verbose_print(verbose, 12, [M, "entering is_amphichiral"])

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
    Given a SnapPy manifold M (assumed to be one-cusped and enhanced
    via enhance_manifold), we wish to update M.exceptions_table.  This
    is a database where the keys are slopes (here s).  The fields are
    useful data about exceptional fillings that we do not want to
    compute twice.  

    Remark: If we fail to compute an invariant, we do not install
    anything in the table - instead we return None.
    """
    verbose_print(verbose, 12, [M, s, "entering exceptions table", field])
    
    allowed_fields = ["fund_gp", "name", "atoroidal_sfs", "reducible", "toroidal"]
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
        out = ft.is_exceptional_due_to_fundamental_group(N, tries, verbose)
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

        out = rt.is_closed_sfs_from_name(name)
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
        out = rt.is_reducible_wrapper(N, tries, verbose)
        M.exceptions_table[s]["reducible"] = out
        verbose_print(verbose, 10, [N, out, 'reducibility'])
        return out
        
    if field == "toroidal":
        out = rt.torus_decomp_wrapper(N, tries, verbose)
        M.exceptions_table[s]["toroidal"] = out
        verbose_print(verbose, 10, [N, out, 'toroidality'])
        return out
        
        
def fetch_volume(M, s, tries=8, verbose=4):
    """
    Given a SnapPy manifold M (assumed to be one-cusped, enhanced, and 
    equipped with a good triangulation) and a slope s (assumed to be 
    hyperbolic), fetch the volume. This means: pull the volume from the 
    table if it is there; else, try to compute it, and then store in the 
    table. Return the volume either way.
    """
    verbose_print(verbose, 12, [M, s, "entering fetch_volume"])

    if s in M.volumes_table:
        verbose_print(verbose, 10, [M, s, 'volume found in table'])
        return M.volumes_table[s]
                
    assert M.solution_type() == 'all tetrahedra positively oriented'

    N = M.copy() 
    N.dehn_fill(s)

    for i in range(tries):
        is_hyp, vol = dunfield.is_hyperbolic_with_volume(N, tries = tries, verbose = verbose)
        if is_hyp:
            verbose_print(verbose, 10, [M, s, 'computed volume on attempt', i+1])
            M.volumes_table[s] = vol
            return vol
    if not is_hyp:
        verbose_print(verbose, -1, [M, s, 'verified volume fail after', tries, 'tries'])
        raise AssertionError

    return M.volumes_table[s]
        

# dealing with a pair of slopes


def are_distinguished_exceptionals(M, s, N, t, tries=8, verbose=5):
    """
    Given a one-cusped SnapPy manifolds M and N, equipped with slopes
    s and t, (where we think that both M(s), N(t) are non-hyperbolic),
    try to distinguish the fillings. Invariants that we check are (in
    order):

    1) Homology
    2) Regina names and Seifert invariants
    3) Irreducibility (via Regina)
    4) Toroidality (via Regina)
    5) Homology groups of covers of small degree
    """
    verbose_print(verbose, 12, [M, s, N, t, 'entering are_distinguished_exceptionals'])

    if ft.are_distinguished_by_homology(M, s, N, t, verbose=verbose):
        return True

    s_name = fetch_exceptional_data(M, s, "name", tries, verbose)
    t_name = fetch_exceptional_data(N, t, "name", tries, verbose)

    verbose_print(verbose, 10, ["comparing", s_name, "to", t_name])

    # Rapid tests that require only s_name and t_name     
    if s_name == t_name:
        # We have no hope of distinguishing this pair.
        return False
    
    if rt.are_distinguished_closed_sfs(s_name, t_name, verbose):
        return True
    if rt.are_distinguished_graph_pairs(s_name, t_name, verbose):
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
    
    # At this point, both manifolds should be reducible, or both
    # toroidal (or we have failed to identify a SFS).    
    # We should probably compare reducible manifolds using their prime decompositions.

    # Tests that search for covers are pretty slow, but effective.                    
    if ft.are_distinguished_by_covers(M, s, N, t, tries, verbose):
        return True
    
    return False        


def are_isometric_fillings(M, s, N, t, tries=8, verbose=4):
    """
    Given cusped SnapPy manifolds M and N, and slopes s and t, try to
    prove that M(s) is isometric to N(t).
    
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
    Given one-cusped, enhanced SnapPy manifolds M and N, compare every
    systole-short Dehn filling of M to the appropriate volume-short
    set of fillings of N.  Find and return the ones that *might*
    produce the same 3-manifold.
    
    Warning: This routine is asymmetric in M and N.
    """
    
    # Initialization for M
    if find_systole_short_slopes(M, tries, verbose) == None:
        # systole computation has failed
        reason = (M.name(), 'systole fail', N.name(), None, None, None)
        return [reason]

    # Initialization for N. This includes homologies of meridional and
    # longitudinal fillings.

    N_vol = fetch_volume(N, (0,0), tries, verbose)
    Q = N.copy()
    Q.dehn_fill(N.m_hom)
    N_mer_base = ft.order_of_torsion(Q)  # Every non-longitudinal filling of N will have torsion homology some multiple of this order.
    Q.dehn_fill(N.l_hom)
    N_long_homology = str(Q.homology())
    N_long_order = ft.order_of_torsion(Q)
    verbose_print(verbose, 12, [N.name(), 'meridional homology', N_mer_base, 'longitudinal homology', N_long_order])

    # Searching through homology hashes for M 
    common_uns = []
    for hom_hash in M.slopes_hyp:
        s0 = list(M.slopes_hyp[hom_hash])[0]  # a representative slope 
        Q = M.copy()
        Q.dehn_fill(s0)
        tor_order = ft.order_of_torsion(Q)
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
                if ft.are_distinguished_by_covers(M, s, N, t, tries, verbose):
                    verbose_print(verbose, 6, [M.name(), s, N.name(), t, 'cover spectrum distinguishes'])
                    continue
                
                reason = (M.name(), s, N.name(), t, M_s_vol, N_t_vol)
                verbose_print(verbose, 2, [reason])
                common_uns.append(reason)
                    
        p = int(tor_order / N_mer_base)  # This will be an integer once we've landed here
        point = (p*N.m_hom[0], p*N.m_hom[1])
        verbose_print(verbose, 25, ['p', p])
        verbose_print(verbose, 25, ['point on Dehn surgery line', point])

        # Compare each filling M(s) for s in M.slopes_hyp[hom_hash] to a set of fillings of N.
        # Every member of this set should have intersection number p with N.l_hom.
        for s in M.slopes_hyp[hom_hash]:
            # find coords of slope s in original framing
            s_orig = gt.preferred_rep((gt.alg_int(s, M.longitude), gt.alg_int(M.meridian, s))) 
            M_s_vol = fetch_volume(M, s, tries, verbose)

            if M_s_vol > N_vol:
                verbose_print(verbose, 12, [M, s, M_s_vol, 'volume too high for common fillings with', N, N_vol])
                continue
            if M_s_vol.overlaps(N_vol):
                reason = (M.name(), s_orig, N.name(), None, M_s_vol, N_vol)
                common_uns.append(reason)
                verbose_print(verbose, 12, [M, s, M_s_vol, 'cannot distinguish volume from', N, N_vol])
                continue
            assert M_s_vol < N_vol

            N_low_vol_slopes = find_low_volume_slopes(N, point, hom_gp, M_s_vol, tries, verbose)
            if len(N_low_vol_slopes) > 0:
                verbose_print(verbose, 6, [M.name(), s, hom_hash, N.name(), N_low_vol_slopes, 'low volume slopes'])
            for t in N_low_vol_slopes:
                N_t_vol = fetch_volume(N, t, tries, verbose)
                if M_s_vol > N_t_vol or M_s_vol < N_t_vol:
                    verbose_print(verbose, 6, [M.name(), s, N.name(), t, 'verified volume distinguishes'])
                    continue
                if ft.are_distinguished_by_covers(M, s, N, t, tries, verbose):
                    verbose_print(verbose, 6, [M.name(), s, N.name(), t, 'cover spectrum distinguishes'])
                    continue

                # find coordinates of t in original framings
                t_orig = gt.preferred_rep((gt.alg_int(t, N.longitude), gt.alg_int(N.meridian, t)))
                
                # Now that we have tried and failed to distinguish,
                # try to prove that they are the same
                if are_isometric_fillings(M, s, N, t, tries, verbose):
                    reason = (M.name(), s_orig, N.name(), t_orig, M_s_vol, 'isometric')
                else:
                    reason = (M.name(), s_orig, N.name(), t_orig, M_s_vol, 'cannot distinguish')
                verbose_print(verbose, 2, [reason])
                common_uns.append(reason)

    return common_uns


def find_common_fillings(M, N, ExcludeS3 = False, tries=8, verbose=4):
    """
    Given one-cusped SnapPy manifolds M and N, we search for common
    Dehn fillings, that is, pairs of slopes s,t such that M(s) might
    be homeomorphic to N(t).
    
    Return a list of tuples - (M, s, N, t, 'reason') where M(s) and N(t)
    are possibly the same manifold. The output should contain the list of
    potential pairs, but might have some fluff (non-distinguished pairs).
    
    If ExcludeS3 == True, then the program does not report an S^3
    common filling (presumably because we already know M and N to be
    knot complements).
    
    This routine is designed for the situation when M != N. If M == N, use 
    check_cosmetic instead.
    """
    mfds = [M, N]
    verbose_print(verbose, 12, [mfds, "entering find_common_fillings"])
    
    # Be liberal in what you accept
    M, N = mfds = [snappy.Manifold(P) for P in mfds]
    
    # but not too liberal.
    for P in mfds:
        if not P.num_cusps() == 1:
            return [(P.name(), None, None, None, 'wrong number of cusps')]

    # Install good hyperbolic metrics on M and N.
    for P in mfds:
        mfd, reason = gt.sanity_check_cusped(P, tries=tries, verbose=verbose)
        if mfd == None:  # failed, so give up
            return [(P.name(), None, None, None, reason)]
        else:  # check and update
            # We found a hyperbolic structure
            assert type(mfd) is snappy.Manifold
            assert mfd.solution_type() == 'all tetrahedra positively oriented'
            P = mfd

    if M.is_isometric_to(N):
        # All their Dehn fillings will coincide
        verbose_print(verbose, 3, [M.name(), N.name(), 'are isometric'])    
        return [(M.name(), None, N.name(), None, 'isometric parent manifolds')]

    # Step two - compute the list of exceptional fillings of both M and N.

    for P in mfds:
        enhance_manifold(P, tries, verbose)  
        find_exceptionals(P, tries, verbose)
        
    # Step three: check for (non-hyperbolic) homeomorphic pairs in 
    # M.slopes_non_hyp and N.slopes_non_hyp.
    # Note that slopes_bad automatically gets recorded and reported.

    bad_uns = []
    for P in mfds:
        for r in P.slopes_bad:
            reason = (P.name(), r, None, None, 'Could not verify hyperbolicity')
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

    # Step five - Merge the lists of common fillings and report output.
    
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
    ### TODO: We really should return the cosmetic slopes in the
    ### original, user-specified, framing.  Currently we return them
    ### in the geometric (aka shortest) framing.
    """
    Given a one-cusped SnapPy manifold M we equip it with a shortest
    framing and then return a list of tuples - (name, s, t, 'reason')
    where s and t are possibly a cosmetic pair.
    
    If use_BoyerLines==True, then we apply the Boyer-Lines theorem:
    the Casson invariant obstructs purely cosmetic surgeries.
    
    If check_chiral==False, then we only check for purely cosmetic 
    surgeries. 

    If check_chiral==True, then we check for chirally cosmetic surgeries
    as well as purely cosmetic ones.
    """
    verbose_print(verbose, 12, [M, "entering check_cosmetic"])
    
    # Be liberal in what you accept
    M = snappy.Manifold(M)

    # but not too liberal.
    if not M.num_cusps() == 1:
        return [(M.name(), None, None, 'wrong number of cusps')]
        
    # If H_1(M) == ZZ, we can apply the Boyer-Lines criterion to rule
    # out purely cosmetic surgeries

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
            s_lens, _ = rt.is_lens_space_from_name(s_name, verbose)
            t_lens, _ = rt.is_lens_space_from_name(t_name, verbose)
            if s_name == "S2 x S1" or s_lens or t_name == "S2 x S1" or t_lens:
                if abs(gt.alg_int(s,t)) > 1:
                    # Cyclic surgery theorem
                    verbose_print(verbose, 2, [s_name, t_name, "distinguished by cyclic surgery theorem"])
                    continue
            
            verbose_print(verbose, 2, [reason])
            bad_uns.append(reason)    

    # Step three: Get the systole of M. Find the systole-short hyperbolic slopes,
    # and split them by homology.
    
    if find_systole_short_slopes(M, tries, verbose) == None:
        # Systole computation has failed. Give up.
        reason = (M.name(), None, None, None, 'systole fail')
        bad_uns.append(reason)
        return bad_uns

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
            print('norm_fac', M.norm_fac.endpoints())

        hom_gp = hom_hash
        s = list(M.slopes_hyp[hom_hash])[0]  # some representative slope
        p = abs(gt.alg_int(s, M.l_hom))
        verbose_print(verbose, 20, [M.name(), hom_hash, s, p])
        
        point = (p*M.m_hom[0], p*M.m_hom[1])
        out = find_low_volume_slopes(M, point, hom_gp, vol_max, tries, verbose)

        # This must be non-empty
        assert len(out) > 0  
        slopes_low_volume[hom_hash] = out
        # and must have M.slopes_hyp[hom_hash] as a subset
        assert (M.slopes_hyp[hom_hash]).issubset(slopes_low_volume[hom_hash])

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
                    
                if ft.are_distinguished_by_covers(M, s, M, t, tries, verbose):
                    continue
                    
                if looks_distinct and not rigorous:
                    reason = (M.name(), s, t, 'distinguished by non-rigorous length spectrum')
                    verbose_print(verbose, -1, [M.name(), s, t, 'distinguished by non-rigorous length spectrum'])
                if not looks_distinct:
                    reason = (M.name(), s, t, 'Not distinguished by hyperbolic invariants or covers')
                verbose_print(verbose, 2, [reason])
                bad_uns.append(reason)

    verbose_print(verbose, 1, [M.name(), 'non-distinguished pairs', bad_uns])
    
    return bad_uns


# "top-level" routines that evaluate lists of manifolds


def check_using_lengths(slopelist, cutoff=3.1, verbose=4, report=20):
    """
    Given a list of tuples of the form (M, s, t) where M is a manifold
    (or a name) and s and t are slopes, checks whether M(s) can be
    distinguished from M(t) using geodesic length spectra up to
    'cutoff'.  This routine is not yet rigorous.
    
    This program tries to distinguish M(s) from M(t) as unoriented
    manifolds.
    
    We presume that M, M(s), and M(t) are all hyperbolic.
    
    Returns a list of tuples that could not be distinguished.

    Example of usage

    sage: import cosmetic_mfds as mfds
    sage: out = mfds.check_mfds(["m135"], verbose=5)
    
    The output tells us that the slopes (1, 3) and (3, 1) are 'not
    distinguished by hyperbolic invariants or covers'.  So we now use
    the (non-rigorous) test check_using_lengths.

    sage: mfds.check_using_lengths([("m135", (1, 3), (3, 1))], verbose = 12)

    The returned value is the empty list, because the length spectrum
    (computed up to length 1.8) distinguishes the two fillings.
    """
    verbose_print(verbose, 12, ["entering check_using_lengths"])
    bad_uns = []
    for n, line in enumerate(slopelist):
        M, s, t = line
        M = snappy.Manifold(M)

        sol_type = M.solution_type()
    
        if sol_type != 'all tetrahedra positively oriented' and sol_type != 'contains negatively oriented tetrahedra':
            verbose_print(verbose, 2, [M, 'bad solution type for unclear reasons.'])
            bad_uns.append((M.name(), None, None, 'bad solution type for unclear reasons'))
            continue
            
        distinct = gt.are_distinguished_by_length_spectrum(M, s, t, check_chiral=True, cutoff = cutoff, verbose=verbose)
        if not distinct:
            verbose_print(verbose, 4, [M, s, t, "not distinguished by length spectrum up to", cutoff])
            bad_uns.append((M.name(), s, t, "not distinguished by length spectrum up to "+str(cutoff) ))
        if n % report == 0: 
            verbose_print(verbose, 0, ["report", n])
            verbose_print(verbose, 0, [bad_uns])
    return bad_uns


def check_list_for_common_fillings(M, manifolds, ExcludeS3 = False, tries=7, verbose=4, report=20):
    """
    Given a cusped SnapPy manifold M (or name), and a list 'manifolds'
    of SnapPy manifolds (or names), check for common Dehn fillings of
    M and one of the manifolds in the list.
    
    Returns a list of tuples containing the slopes that give
    (confirmed or suspected) common fillings.
    
    If ExcludeS3 == True, then the program does not report an S^3
    common filling (presumably because the user already knows M and N 
    are knot complements).

    Example of usage

    sage: import snappy
    sage: L = snappy.AlternatingKnotExteriors()
    sage: M = snappy.Manifold("4_1")
    sage: import cosmetic_mfds as mfds
    sage: mfds.check_list_for_common_fillings(M, L[0:5], ExcludeS3 = True)

    This returns the following list:
    
    [('3a1', None, None, None, 'is a torus knot'),
     ('4_1', None, '4a1', None, 'isometric parent manifolds'),
     ('4_1', (5, -1), '5a1', (5, 1), 0.9813688288922?, 'isometric'),
     ('4_1', (5, 1), '5a1', (5, 1), 0.9813688288922?, 'isometric'),
     ('4_1', (1, 2), '5a1', (1, -1), 1.3985088841508?, 'isometric'),
     ('4_1', (1, -2), '5a1', (1, -1), 1.3985088841508?, 'isometric'),
     ('4_1', None, '5a1', (8, 1), 2.0298832128193?, 2.0298832128193?),
     ('5a2', None, None, None, 'is a torus knot')]

    The program reports four common fillings between 4_1 (the
    figure-eight knot) and 5a1 (the 5_2 knot).  The program fails to
    show that 5a1(8, 1) is not isometric to a filling of the
    figure-eight knot.  See Theorem 5.1 (and its proof) in our paper
    'Excluding cosmetic surgeries on hyperbolic 3-manifolds'.
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

    * amphichiral_uns is a list of undistinguished amphichiral pairs
        (M, s) and (M, t) where s and t are exchanged by an
        orientation-reversing symmetry of M (hyperbolic) and where
        M(s) was not distinguished from M(t).

    * bad_uns is a list of non-hyperbolic manifolds and then pairs
       (M,s) and (M, t) where s and t are _not_ exchanged by an
       orientation-reversing symmetry of M where M(s) was not
       distinguished from M(t).  The cosmetic surgery conjecture
       predicts that this second part of the list should be empty.

    Example of usage: 

    sage: import snappy
    sage: import cosmetic_mfds as mfds
    sage: L = snappy.OrientableCuspedCensus(num_cusps=1)
    sage: mfds.check_mfds(L[0:200], verbose=5)
    
    This returns the following output:

    ([('m135', (1, 3), (3, 1), 'Not distinguished by hyperbolic invariants or covers'),
      ('m207', (0, 1), (1, 0), 'L(3,1) # L(3,1)', 'L(3,1) # L(3,1)')],
     [('m172', (0, 1), (1, 1), 'L(49,18)', 'L(49,18)')])
     
    Note that none of the above is a purely cosmetic filling.
    Compare Theorem 4.4 (and its proof) in "Excluding cosmetic surgeries on hyperbolic 3-manifolds".
    """
    
    verbose_print(verbose, 12, ["entering check_mfds"])
    amphichiral_uns = []
    bad_uns = []
    for n, M in enumerate(manifolds):
        M = snappy.Manifold(M)

        is_hyp, reason = gt.is_likely_hyperbolic(M, verbose)
        if not is_hyp:
            bad_uns.append((M.name(), None, None, reason, None))
            continue
        
        uns = check_cosmetic(M, use_BoyerLines=use_BoyerLines, check_chiral=False, tries=tries, verbose=verbose)
        if len(uns) > 0:
            is_amph, cob = is_amphichiral(M, tries=tries, verbose=verbose)
            if is_amph:
                for line in uns:
                    s = line[1]
                    t = line[2]
                    filled_name = line[3]
                    if rt.is_chiral_graph_mfd_from_name(filled_name) and gt.preferred_rep(cob*vector(s)) == t:
                        # The slopes s and t are interchanged by symmetry, and the filled manifold is chiral
                        verbose_print(verbose, 2, ['chiral filling on amph manifold:', M.name(), s, t, filled_name])
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
    Checks a list of SnapPy manifolds (or names) for both purely and
    chirally cosmetic surgeries.  (You should probably have already
    run the list through check_mfds.)
    
    Returns a list of amphichiral manifolds (which are not checked)
    and a list of pairs of slopes (M, s) and (M, t), where M is chiral,
    such that the program could not distinguish M(s) from M(t).

    We note that if M is amphichiral, and M(s), M(t) is a chirally
    cosmetic pair, then M(s), M(-t) will be a purely cosmetic
    pair. Thus any "exotic" chirally cosmetic pair of slopes should
    have already been found by running M through check_mfds(...).
    
    Example of usage:
    
    sage: import snappy
    sage: import cosmetic_mfds as mfds
    sage: L = snappy.OrientableCuspedCensus(num_cusps=1)
    sage: mfds.check_mfds_chiral(L[0:200], verbose=5)
    
    This returns the following output:

    (['m003', 'm004', 'm135', 'm136', 'm206', 'm207'],
     [('m172', (0, 1), (1, 1), 'L(49,18)', 'L(49,18)')])    
    """    
    verbose_print(verbose, 12, ["entering check_mfds_chiral"])
    bad_uns = []
    amphichiral_uns = []
    for n, M in enumerate(manifolds):
        M = snappy.Manifold(M)

        is_hyp, reason = gt.is_likely_hyperbolic(M, verbose)
        if not is_hyp:
            bad_uns.append((M.name(), None, None, reason))
            continue

        is_amph, cob = is_amphichiral(M, tries=tries, verbose=verbose)
        if is_amph:
            verbose_print(verbose, 2, [M.name(), "is amphichiral; skipping."])
            amphichiral_uns.append(M.name())
            continue

        uns = check_cosmetic(M, use_BoyerLines=False, check_chiral=True, tries=tries, verbose=verbose)
        bad_uns.extend(uns)
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n])
            verbose_print(verbose, 0, ['Amphichiral mfds:', amphichiral_uns])
            verbose_print(verbose, 0, ['Bad slopes:', bad_uns])
    return amphichiral_uns, bad_uns
