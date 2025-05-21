#
# geom_tests.py
#

# This file contains utility code that applies various topological and
# geometric tests for dealing with slopes and determining the
# geometric type of the filling. It also contains code for
# distinguishing two fillings from one another using geometry.  The
# main organizing principle is: routines land here if they use
# geometry, and especially if geometrization is used. 

import snappy
import regina
import dunfield
import fundamental as ft
import regina_tests as rt

from verbose import verbose_print

# Math 

from sage.functions.log import exp
from sage.functions.other import sqrt, ceil, floor
from sage.arith.misc import gcd, xgcd, factor, next_prime
from sage.symbolic.constants import pi
from sage.symbolic.ring import SR
from sage.modules.free_module_element import vector
from sage.rings.real_mpfr import RR
from sage.rings.real_mpfi import RIF


# sanity checks


# The following test is non-rigorous. It is designed to produce a flag that
# none of the rigorous tests have succeeded. We should not rely on it beyond that.
def is_exceptional_due_to_volume(M, verbose = 3):
    verbose_print(verbose, 12, [M, "entering is_exceptional_due_to_volume"])
    if M.volume() < 0.9:  # smaller than volume of Weeks manifold
        verbose_print(verbose, -1, [M, "has volume too small...(NON-RIGOROUS)"])
        verbose_print(verbose, 6, [M.fundamental_group()])
        return True

def is_likely_hyperbolic(M, verbose = 3):
    """
    Given a SnapPy manifold M (or name) does a quick and dirty test to
    see if M is probably hyperbolic.  If it is, return (True, None).
    If it isn't, return (False, reason).
    """    
    M = snappy.Manifold(M)    
    sol_type = M.solution_type()
    
    if sol_type == 'all tetrahedra positively oriented' or sol_type == 'contains negatively oriented tetrahedra':
        return (True, None)

    # So M is probably not a hyperbolic manifold. Try to identify it.
        
    kind, found_name = dunfield.identify_with_bdy_from_isosig(M)
    if kind != 'unknown':
        verbose_print(verbose, 2, [M.name(), kind, found_name])
        reason = found_name
    elif is_exceptional_due_to_volume(M, verbose):   
        verbose_print(verbose, 2, [M.name(), 'NON-RIGOROUS TEST says volume is too small']) 
        reason = 'small volume'
    else:
        verbose_print(verbose, 2, [M, 'bad solution type for unclear reasons.'])
        reason = 'bad solution type for unclear reasons'

    return (False, reason)


def is_knot_manifold(M):
    """
    Given a snappy Manifold M, returns True if and only if M is a knot
    manifold: has one (unfilled) cusp, is orientable, and has H_1(M) = Z.
    """    
    # The complement of a knot in S^3 is connected, 'compact',
    # orientable, has one torus boundary component, and has homology
    # equal to Z.

    # Anything else?  Eg a special Alexander polynomial?  Place quick
    # and easy tests here.

    if M.num_cusps() != 1:
        return False
    if M.cusp_info()[0].filling != (0,0):
        return False    
    if not M.is_orientable():
        return False
    if M.homology().__repr__() != 'Z': 
        return False
    return True


def sanity_check_cusped(M, tries=10, verbose=3):
    """
    Accepts a manifold M, presumed to be one-cusped and hyperbolic.
    Performs some sanity checks, such as the number of cusps.

    If M is hyperbolic, returns M (with positive triangulation).
    If M seems non-hyperbolic, returns None and an error code.
    """
    if not M.num_cusps() == 1:
        return (None, 'wrong number of cusps')

    sol_type = M.solution_type()
    if sol_type == 'all tetrahedra positively oriented':
        verbose_print(verbose, 10, [M, 'already positively oriented'])
        return (M, None)
        
    elif sol_type == 'contains negatively oriented tetrahedra':
        X = dunfield.find_positive_triangulation(M, tries=tries, verbose=verbose)
        if X == None:
            verbose_print(verbose, 5, [M, 'positive triangulation fail'])
            return (None, 'positive triangulation fail')
        else: # we have succeeded
            verbose_print(verbose, 10, [M, 'found positive triangulation'])
            return (X, None)
        
    else:   
        # So M is probably not a hyperbolic manifold.  Let's do a few
        # quick tests to help ourselves later, and then give up.

        if ft.is_torus_link_filling(M, verbose):
            # This is useful information for cosmetic surgeries
            verbose_print(verbose, 4, [M, 'is a torus link filling'])
            return (None, 'is a torus knot')
        if ft.is_exceptional_due_to_fundamental_group(M, tries, verbose):
            verbose_print(verbose, 4, [M, 'exceptional due to fundamental group'])
            return (None, 'exceptional due to fundamental group')
            
        out = rt.is_toroidal_wrapper(M, verbose)
        if out[0]:
            # M is toroidal so use the torus decomposition as the 'reason'
            verbose_print(verbose, 4, [M, 'is toroidal'])
            return (None, 'toroidal mfd: ' + str(out[1]))
        # Anything else is confusing
        if is_exceptional_due_to_volume(M, verbose):   
            verbose_print(verbose, -1, [M, 'NON-RIGOROUS TEST says volume is too small']) 
            return (None, "volume too small")
        verbose_print(verbose, -1, [M, 'bad solution type for unclear reasons...'])
        return (None, "bad solution type")


def is_reasonable_interval(x, precision = 0.01):
    """
    Given a real interval x, check whether the endpoints of x are closer than precision.
    """
    return (x.upper() - x.lower() < precision)


# cusp utilities


def alg_int(u, v):
    """
    Given two slopes, compute their algebraic intersection number.
    """
    a, b = u
    c, d = v
    return a*d - b*c


def preferred_rep(t):
    """
    Find the preferred representative of a slope in QP^1.
    """
    a, b = t
    out = (a,b)
    if a < 0 or (a == 0 and b < 0):
        out = (-a, -b)
    return out


def a_shortest_lattice_point_on_line(point, direction, m, l, verbose=3):
    """
    Given a pair of lattice points (point, direction) and holonomies
    m, l, returns the lattice_point on the determined line closest to
    the origin.  Note - if there is a tie for closest then we return
    one of the two.
    """
    a, b = point
    c, d = direction
    # Let \Lambda \subset \CC be the lattice generated by m and l.
    # Let L' be the line in \Lambda through a*m + b*l in the direction
    # c*m + d*l.  We must find the point of L' which is closest to the
    # origin.  If we divide \Lambda and L' by c*m + d*l then L'
    # becomes horizontal, and the lattice points of L' are now distance one
    # apart.  The points of L' now have the form (a*m + b*l - k(c*m +
    # d*l))/(c*m + d*l), for k an integer.  We must minimise the real
    # part.
    real_part = ((a*m + b*l)/(c*m + d*l)).real()
    rounded_part = real_part.round() #
    # We want the closest integer to rounded_part, but the left and round endpoints got rounded separately.
    left = int(rounded_part.lower())
    right = int(rounded_part.upper())
    verbose_print(verbose, 12, ["Real_part", real_part.endpoints(), "left", left, "right", right])
    # If left and right are too separated (because real_part is a
    # giant interval), we give up and crash.
    if right - left > 1:
        verbose_print(verbose, 5, ["Not enough precision to get single slope"])
        raise
    # If left and right are separated by 1 (because real_part contains
    # a half integer), we compute both slopes and figure out which is shorter.
    candidates = [(abs((a-k*c)*m + (b-k*d)*l).endpoints(), k) for k in range(left, right+1)]
    candidates.sort()
    
    k = candidates[0][-1] # Whichever of left or right has the shorter slope
    return preferred_rep((a - k*c, b - k*d))


def shortest_complement(t, m, l):
    """
    Given a primitive slope t and the holonomies of the current
    meridian and longitude, returns a shortest complementary slope s
    so that s.t = +1.
    """
    c, d = t # second slope
    _, a, b = xgcd(d, c) # first slope
    b = -b
    assert a*d - b*c == 1
    return a_shortest_lattice_point_on_line((a, b), (c, d), m, l)


def cusp_invariants(M, prec=80, tries=10, verbose=3):
    """
    Given a snappy manifold with one cusp, returns the holonomies of
    the current meridian and longitude, and also the square root of
    the area.
    """
    # Note - this uses the current framing, whatever it is
    # Precision gets doubled before we do anything.
    for i in range(tries):
        prec = prec * 2
        try:
            [(m,l)] = M.cusp_translations(verified = True, bits_prec = prec)
            verbose_print(verbose, 12, [M, 'computed cusp translations at precision', prec])
            if is_reasonable_interval(m.real()) and is_reasonable_interval(m.imag()) and is_reasonable_interval(l.real()) and is_reasonable_interval(l.imag()):
                break
        except:
            verbose_print(verbose, 10, [M, 'failed to find cusp translations at precision', prec])

    norm_fac = sqrt(l * m.imag())
    return m, l, norm_fac


# Get a list of short slopes


def find_short_slopes(M, len_cutoff=None, normalized=False, tries=10, verbose=3):
    """
    Given a hyperbolic manifold M (assumed to have one cusp) finds all
    slopes that are shorter than length six.  If length_cutoff is
    given then finds all slopes on the cusp that are shorter than
    len_cutoff.
    
    The Boolean flag 'normalized' clarifies whether the length cutoff
    is normalized (in the sense of Hodgson-Kerckhoff). If true, we
    convert to un-normalized, geometric length.

    Note that if len_cutoff is not given, then the normalized flag is
    ignored.
    """
    verbose_print(verbose, 12, [M, 'entering find_short_slopes'])

    if len_cutoff == None:
        # Go up to Euclidean length 6
        len_cutoff = 6.0
        normalized = False
        
    if normalized:
        p = next_prime(floor(len_cutoff**2))
        slopes_expected = p+1
        # The intersection number between a pair of slopes is at most floor(len_cutoff^2).
        # Agol's Lemma says: find the next prime p, then the number of slopes is at most  p + 1.
        # Note that by Chebyshev's Theorem, we have p < 2*floor(len_cutoff^2). This is a massive over-estimate.
        verbose_print(verbose, 12, [M, 'expecting at most', slopes_expected, 'slopes of norm_length less than', len_cutoff])
        
        _, _, norm_fac = cusp_invariants(M, tries=tries, verbose=verbose)            
        len_cutoff = len_cutoff * norm_fac
        # len_cutoff = len_cutoff * norm_fac.center()  
        # norm_fac.center is a hackity-hack which stayed until the
        # systole became verified.  Now that it becomes verified, we can feed
        # M.short_slopes an RIF as a length.
    else:
        p = next_prime(floor(len_cutoff**2 /3.35))
        slopes_expected = p+1
        # The intersection number between a pair of slopes is at most floor(len_cutoff^2 / Area).
        # The cusp area is at least 3.35 by Cao-Meyerhoff (improved to 2*sqrt(3) by GHMTY).
        # Agol's Lemma says: find the next prime p, then the number of slopes is at most  p + 1.
        verbose_print(verbose, 12, [M, 'expecting at most', slopes_expected, 'slopes of length less than', len_cutoff])

    prec = 40 # note the magic number 40.
    for i in range(tries):
        prec = prec * 2
        try:
            slopes = M.short_slopes(len_cutoff, verified = True, bits_prec=prec)[0]
            if len(slopes) > slopes_expected:
                # Accuracy is too low
                continue
            else:
                verbose_print(verbose, 12, [M, 'managed to find', len(slopes), 'short slopes at precision', prec])
                break
        except:
            verbose_print(verbose, 10, [M, 'failed to find short slopes at precision', prec])
            
    slopes = [preferred_rep(s) for s in slopes]
    return set(slopes)


# unverified systole

# The next set of functions should get ripped out.

def systole_with_covers(M, tries=10, verbose=3):
    """
    Given a snappy Manifold M,
    try to compute a lower bound for the systole.
    If direct computation fails, then try taking covers.
    The idea is that the systole of M is at least (1/n) times
    the systole of an n-fold cover.
    We only care about systoles that are shorter than 0.15.
    """    
    verbose_print(verbose, 12, [M, "entering systole_with_covers"])

    retriang_attempts = 2*tries
    # This is a hack. In our context, tries is at most 8. But here, we want 
    # to retriangulate many times, until we succeed.


    for deg in range(1, 6):
        cov = M.covers(deg)
        for N in cov: 
            for i in range(retriang_attempts): # that looks like a magic number... 
                for j in range(i):
                    N.randomize() # This should probably be done with isosigs.
                try:
                    sys = systole(N, verbose = verbose)
                    verbose_print(verbose, 10, ['systole of', deg, 'fold cover', N, 'is at least', sys])
                    return (sys/deg)
                except:
                    sys = None
                    verbose_print(verbose, 10, [N, 'systole failed on attempt', i])

    if sys == None:
        verbose_print(verbose, 6, [M, 'systole fail'])
        return None


def systole_with_tries(M, tries=10, verbose=3):
    """
    Given a snappy Manifold M, tries and tries again to compute a lower
    bound for the systole. Builds in randomization.
    """
    verbose_print(verbose, 12, [M, 'entering systole_with_tries'])

    # Before trying hard things, see if we get lucky.
    try:
        sys = systole(M, verbose=verbose)
        verbose_print(verbose, 10, [M, sys, 'systole computed on first attempt'])
        return sys
    except:
        sys = None
        verbose_print(verbose, 10, [M, 'systole failed on first attempt'])
    
    # Build a database of isosigs
    N = snappy.Manifold(M)
    retriang_attempts = 10*tries # Magic constant
    isosigs = set()
    for i in range(retriang_attempts):
        N.randomize()
        isosigs.add(N.triangulation_isosig())
    verbose_print(verbose, 15, [M, 'isosigs:', isosigs])
    verbose_print(verbose, 10, [M, len(isosigs), 'isosigs found'])
        
    for sig in isosigs:
        N = snappy.Manifold(sig)
        try:
            sys = systole(N, verbose=verbose)
            verbose_print(verbose, 10, [M, sys, 'systole computed from', sig])
            return sys
        except:
            sys = None
            verbose_print(verbose, 10, [M, 'systole failed on', sig])

    if sys == None:
        verbose_print(verbose, 2, [M, 'systole fail'])
        return None



def systole(M, verbose = 3):
    """
    Given a snappy Manifold M,
    tries to compute the systole of M, non-rigorously (for now).
    We only care about systoles that are shorter than 0.15.
    
    N.length_spectrum() might cause this routine to crash, so usage should be wrapped in a 'try'.
    """
    N = M.high_precision()
    verbose_print(verbose, 12, [M, "entering systole"])
    spec = N.length_spectrum(0.15, full_rigor = True) # Not actually rigorous
    verbose_print(verbose, 12, [M, "computed length spectrum"])
    if spec == []:
        return 0.15 # any systole larger than this gets ignored. 
    else:
        return spec[0].length.real()


### Verified systole

def surgery_description(M, drilling_length=0.4, tries=10, verbose=3):
    """
    Given a snappy Manifold M, tries to find a surgery description of M by 
    drilling and filling generators of the fundamental group.
    The parameter drilling_length controls what should be drilled.
    
    Returns surgery description if successful or M itself if not.
    """

    verbose_print(verbose, 12, [M, "entering surgery_description"])
    G = M.fundamental_group(False)
    verbose_print(verbose, 10, [M, G])
    real_len, g = min((real_len, g) for g in G.generators() if (real_len := G.complex_length(g).real()) > 1e-6)
    verbose_print(verbose, 10, [M, real_len, g])
    if real_len < drilling_length:
        try:
            N = M.drill_word(g, verified=True, bits_prec=1000)
        except:
            return M
        N.dehn_fill((1,0),-1)
        N = dunfield.find_positive_triangulation(N, tries, verbose)
        if N.solution_type() == 'all tetrahedra positively oriented':
            return N
    return M

def verified_systole(M, cutoff=None, bits_prec=300, verbose = 3):
    """
    Given a snappy Manifold M, tries to compute a verified interval 
    containing the systole of M.
    Returns the systole in RIF form.
    The bits_prec variable controls precision.
    If cutoff != None, only looks for systoles up to the given value.
    (In many applications, we only care about systoles that are shorter than 0.15.)
    
    If M contains short geodesics that are not filled cusps, this might also run 
    for a very long time. If this is a possibility, we recommend running 
    verified_systole_with_drilling.
    """
    
    verbose_print(verbose, 12, [M, "entering verified_systole"])
    if cutoff == None:
        try:
            spec = M.length_spectrum_alt(count=1, bits_prec=bits_prec, verified=True)
            verbose_print(verbose, 10, [M, 'length spectrum up to first curve', spec])
            return spec[0].length.real()
        except:
            verbose_print(verbose, 10, [M, 'systole failed to compute'])
            return None
    else:
        spec = M.length_spectrum_alt(max_len=cutoff, bits_prec = bits_prec, verified = True)
        verbose_print(verbose, 10, [M, 'length spectrum up to cutoff', cutoff, spec])
        
    if spec != []: # some geodesics were found
        return spec[0].length.real()
    else:  # no geodesics shorter than 0.15
        return RIF(cutoff)


def verified_systole_with_drilling(M, cutoff=None, bits_prec=300, tries=10, verbose=3):
    """
    Given a snappy Manifold M, drills and re-fills short curves, then
    tries to compute a verified interval containing the systole of M.
    Returns the systole in RIF form.
    If cutoff != None, only looks for systoles up to the given value.
    (In many applications, we only care about systoles that are shorter than 0.15.)
    """

    verbose_print(verbose, 12, [M, "entering verified_systole"])
    N = surgery_description(M, tries=tries, verbose = verbose)
    return verified_systole(N, cutoff=cutoff, bits_prec=bits_prec, verbose=verbose)


def verified_spectrum_with_tries(M, cutoff, initial_prec=100, tries=8, verbose=3):

    prec = initial_prec
    for i in range(tries):
        try:
            M_spec = M.length_spectrum_alt(max_len = cutoff, bits_prec = prec, verified=True)
            verbose_print(verbose, 10, [M, 'found spectrum at precision', prec])
            return M_spec
        except Exception as e:
            verbose_print(verbose, 10, [M, 'precision =', prec, e])
        prec = prec + 100
    return None
            

# def verified_systole_with_tries(M, bits_prec=60, tries=10, verbose=3):
#     """
#     Given a snappy Manifold M, tries and tries again to compute a 
#     verified systole. Builds in randomization.
#     """
#     verbose_print(verbose, 12, [M, 'entering verified systole_with_tries'])
# 
#     # Before trying hard things, see if we get lucky.
#     try:
#         sys = verified_systole(M, bits_prec=bits_prec, verbose=verbose)
#         verbose_print(verbose, 10, [M, sys, 'systole computed on first attempt'])
#         return sys
#     except:
#         sys = None
#         verbose_print(verbose, 10, [M, 'systole failed on first attempt'])
#     
#     # Build a database of isosigs
#     N = snappy.Manifold(M)
#     retriang_attempts = 10*tries # Magic constant
#     isosigs = set()
#     for i in range(retriang_attempts):
#         N.randomize()
#         isosigs.add(N.triangulation_isosig())
#     verbose_print(verbose, 15, [M, 'isosigs:', isosigs])
#     verbose_print(verbose, 10, [M, len(isosigs), 'isosigs found'])
#         
#     for sig in isosigs:
#         N = snappy.Manifold(sig)
#         try:
#             sys = verified_systole(N, bits_prec=bits_prec, verbose=verbose)
#             verbose_print(verbose, 10, [M, sys, 'systole computed from', sig])
#             return sys
#         except:
#             sys = None
#             verbose_print(verbose, 10, [M, 'systole failed on', sig])
# 
#     if sys == None:
#         verbose_print(verbose, 2, [M, 'systole fail'])
#         return None




# Finding S3 slope
 

def get_S3_slope_hyp(M, verify_on=True, covers_on=True, regina_on=True, tries = 10, verbose=3): 
    """
    Given M, a hyperbolic knot manifold, returns the slope that gives
    S^3, if there is one.  We also return several booleans.
    """
    verbose_print(verbose, 12, [M, 'entering get_S3_slope_hyp'])

    is_knot = False
    geometrically_easy = True
    regina_easy = True

    if not(is_knot_manifold(M)):
        return None, is_knot, geometrically_easy, regina_easy

    # Before doing anything else, check if (1,0) slope does it
    N = snappy.Manifold(M)
    r=(1,0)
    N.dehn_fill(r)
    exceptional, type_except = ft.is_exceptional_due_to_fundamental_group(N, tries, verbose)
    if type_except=='S3':
        verbose_print(verbose, 5, ['Lucky guess:', M, r, 'has trivial fundamental group'])
        is_knot = True
        return r, is_knot, geometrically_easy, regina_easy

    # Now, try using geometry
    M = dunfield.find_positive_triangulation(M, tries, verbose)
    
    if M.solution_type() != 'all tetrahedra positively oriented':
        verbose_print(verbose, 10, ['Bad triangulation:', M, M.solution_type()])
        geometrically_easy = False
            
    six_theorem_length = 6.01 # All exceptionals shorter than this
    short_slopes_all = find_short_slopes(M, six_theorem_length, normalized=False, verbose=verbose)
    short_slopes = []
    short_slopes_hard = []
    long = M.homological_longitude()
    
    ## We take through passes through the list of slopes, ordered by speed.
    ## Pass #1: Homology (very fast)
    ## Pass #2: Fundamental group, covers, hyperbolic structure, regina_name
    ## Pass #3: Regina three-sphere recognition.
    
    for r in short_slopes_all:
        # Compute homology via intersection number with longitude
        if abs(alg_int(long,r)) != 1:
            verbose_print(verbose, 10, [M, r, 'ruled out by homology'])
        else:
            short_slopes.append(r)
            
    for r in short_slopes:
        N = snappy.Manifold(M)
        N.dehn_fill(r)

        # Fundamental group
        
        exceptional, type_except = ft.is_exceptional_due_to_fundamental_group(N, tries, verbose)
        if type_except=='S3':
            verbose_print(verbose, 5, [M, r, 'has trivial fundamental group'])
            is_knot = True
            return r, is_knot, geometrically_easy, regina_easy
        if type_except in ['S2 x S1', 'Free group', 'Lens', 'Has lens space summand']:
            verbose_print(verbose, 10, [M, r, 'has nontrivial fundamental group'])
            continue
            
        # There are other exceptional types where the group may or may not be trivial.

        # Verified hyperbolicity (skip this if we know the slope is exceptional)
        if verify_on and not(exceptional):
            structure_found = dunfield.is_hyperbolic(N, 2*tries, verbose) # Nathan randomises for us.
            if structure_found: 
                verbose_print(verbose, 10, [M, r, 'hyperbolic structure found'])
                continue

        # Covers
        # Checking degree 5 and 7 only seems to speed things up by 20%?
        if covers_on: 
            verbose_print(verbose, 12, [M, r, 'Trying covers.'])
            cover_found = False
            for i in range(2, 7):
                verbose_print(verbose, 12, ['searching in degree', i])
                if N.covers(i) != []: 
                # Old comment: method='gap' is much faster
                # New comment: probably not faster?
                    cover_found = True
                    verbose_print(verbose, 10, [M, r, 'has a cover of degree', i])
                    break
            if cover_found: continue

        # Easy Regina: try to find the name in a lookup table.
        verbose_print(verbose, 12, ['Trying Regina name search on', M, r])
        name = dunfield.regina_name(N)
        if name=='S3':
            verbose_print(verbose, 10, [M, r, 'is recognized as S3 triangulation'])
            is_knot = True   
            return r, is_knot, geometrically_easy, regina_easy
        if name != None:
            verbose_print(verbose, 10, [M, r, 'is recognized as', name])
            continue
        
        short_slopes_hard.append(r)

    # Now, try the hard stuff.
    regina_easy = False
    for r in short_slopes_hard:
        N = snappy.Manifold(M)
        N.dehn_fill(r)
        if regina_on:
            verbose_print(verbose, 10, ['Using Regina sphere recognition on', M, r])
            isosigs = dunfield.closed_isosigs(N, tries = 25, max_tets = 25)
            if len(isosigs) == 0:
                continue  # Regina will not be of any use to us
            T = dunfield.to_regina(isosigs[0])
            out = T.isThreeSphere()
            if out: 
                verbose_print(verbose, 0, ['Regina sphere recognition succeeded on', M, r])
                # This has never printed.  As always, the fundamental group
                # catches all three-spheres.  Why?
                is_knot = True
                return r, is_knot, geometrically_easy, regina_easy
            else:
                continue
                # Perhaps also try reducible, toroidal tests here?

        # Other ideas to prove the manifold is not a three-sphere: 

        # 1) Build the Dirchlet domain and prove the child is
        # hyperbolic.  [Actually - verify seems to catch all
        # hyperbolic children - so this is not worth the effort.]

        # 2) Look for a splitting torus, and certify the pieces. I
        # guess that this will catch almost all of the remaining
        # non-spheres.  If the torus could be guessed... say using
        # M.normal_boundary_slopes() on the parent M?

        # 3) Instead of listing _all_ covers, try to guess just one.

        # 3') Use the volume (positive versus zero) or other
        # properties of the manifold to decide how far to look for
        # covers...

        # 4) Use the fact that the parent is hyperbolic to get a
        # non-trivial linear rep of the child???  Hmmm.  Look at
        # PSL(2,q)?  What does Nathan's paper with Thurston suggest?

        # 5) In the atoroidal case, the remaining non-spheres will be
        # small SFSs (which are homology spheres).  Can the SFS
        # structure be guessed?  Perhaps from the fundamental group?
        # [This seems to be caught by Regina name already.]

        # 6) Try to find a nice PSL(2,R) rep?
        
    return None, is_knot, geometrically_easy, regina_easy            


# Geometry of fillings


def is_hyperbolic_filling(M, s, m, l, tries, verbose):
    """
    Given a one-cusped manifold M (assumed hyperbolic), a slope s,
    and holonomies m, l of the meridian and longitude,
    try to determine if M(s) is hyperbolic or exceptional.  Returns
    True or False respectively, and returns None if we failed.
    """
    verbose_print(verbose, 12, [M, s, "entering is_hyperbolic_filling"])
    p, q = s

    # It is not clear that we should bother with the six-theorem
    if abs(p*m + q*l) > RIF( 6 ): # six-theorem
        return True

    N = snappy.Manifold(M)
    N.dehn_fill(s)

    for i in range(tries):
        for j in range(i+1):
            if i > 0:
                N.randomize()
            is_except, reason = ft.is_exceptional_due_to_fundamental_group(N, 3, verbose)
            if is_except:
                verbose_print(verbose, 5, [N, "Is exceptional due to group,", reason])
                return False
        for j in range(1): # this is not a typo,
            # because Nathan iterates and randomizes for us
            if dunfield.is_hyperbolic(N, i+2, verbose): 
                return True
        if i > 0: # gosh, this is a tricky one... so
            if rt.is_reducible_wrapper(N, tries, verbose)[0]:
                return False 
            if rt.is_toroidal_wrapper(N, verbose)[0]:
                return False 
            name = dunfield.regina_name(N)
            if name != None and name[:3] == 'SFS': # We trust the regina_name.
                return False
    return None


# Dealing with a pair of slopes

def distinct_sets_of_rifs(set1, set2):
    """
	Given two (sets or lists) of (real or complex) RIFs, checks whether there is an element
	of one set that is verifiably distinct from all elements of the other.
	"""
	
    for v1 in set1:
       if all(v1 != v2 for v2 in set2):
           return True
    for v2 in set2:
       if all(v1 != v2 for v1 in set1):
           return True
    return False


def are_distinguished_by_length_spectrum(Ms, Mt, check_chiral=False, tries=5, cutoff = 1.0, verbose=5):
    """
    Given a pair of hyperbolic manifold Ms and Mt, try to distinguish them 
    using the (verified) complex length spectra.
    
    If check_chiral==False, then we only check for orientation-preserving
    isometries.
    If check_chiral==True, then we check for both orientation-preserving and
    orientation-reversing isometries.
    
    The cutoff variable determines how far into the length spectrum we bother checking.
    To save computer time, we recommend tring lower cutoffs before trying higher ones.
    
    Returns True if the manifolds are distinguished, and False if not. 
    """

    verbose_print(verbose, 12, [Ms, Mt, 'entering are_distinguished_by_length_spectrum'])
        
    Ms_spec = verified_spectrum_with_tries(Ms, cutoff, tries=tries, verbose=verbose)
    Mt_spec = verified_spectrum_with_tries(Mt, cutoff, tries=tries, verbose=verbose)
    
    if Ms_spec == None or Mt_spec == None:
        verbose_print(verbose, 6, [Ms, Mt, 'could not compute spectra'])
        return False

    Ms_lengths = [line.length for line in Ms_spec]
    Mt_lengths = [line.length for line in Mt_spec]
    Mt_conjugates = [length.conjugate() for length in Mt_lengths]
    
    verbose_print(verbose, 15, [Ms, Ms_lengths])
    verbose_print(verbose, 15, [Mt, Mt_lengths])
    
    if not(check_chiral) and distinct_sets_of_rifs(Ms_lengths, Mt_lengths):
        verbose_print(verbose, 6, [Ms, Mt, 'length spectrum up to', cutoff, 'distinguishes oriented manifolds'])
        return True
    if check_chiral and distinct_sets_of_rifs(Ms_lengths, Mt_lengths) and distinct_sets_of_rifs(Ms_lengths, Mt_conjugates):
        verbose_print(verbose, 6, [Ms, Mt, 'length spectrum up to', cutoff, 'distinguishes un-oriented manifolds'])
        return True
        
    verbose_print(verbose, 8, [Ms, Mt, 'length spectrum up to', cutoff, 'failed to distinguish'])
    return False


def are_distinguished_by_hyp_invars(M, s, t, tries, verbose):
    """
    Given a cusped manifold M and two slopes s and t (where we think
    that both fillings are hyperbolic), try to prove that M(s) is not
    orientation-preservingly homeomorphic to M(t).
    
    Returns True if we can rigorously tell the manifolds apart.
    """

    verbose_print(verbose, 12, [M, s, t, 'entering are_distinguished_by_hyp_invars'])
    Ms = snappy.Manifold(M)
    Mt = snappy.Manifold(M)
    Ms.dehn_fill(s)
    Mt.dehn_fill(t)
    Ms = dunfield.find_positive_triangulation(Ms, tries) 
    Mt = dunfield.find_positive_triangulation(Mt, tries)

    if Ms == None or Mt == None:
        verbose_print(verbose, 6, [M, s, t, 'positive triangulation fail'])
        return None
    
    prec = 40 # note the magic number 20.  Fix.
    for i in range(tries):
        try:
            # Try ordinary volume first
            Ms_vol = Ms.volume(verified=True, bits_prec = prec)
            Mt_vol = Mt.volume(verified=True, bits_prec = prec)

            if Ms_vol < Mt_vol or Mt_vol < Ms_vol:
                verbose_print(verbose, 6, [M, s, t, "verified volume distinguishes at precision", prec])
                return True
            else:
                verbose_print(verbose, 6, [M, s, t, "volumes very close at precision", prec])
        except Exception as e:
            verbose_print(verbose, 6, [M, s, t, "failed to compute volume at precision", prec, str(e)])

        prec = prec * 2 # seems that complex volume needs more precision than regular...
            
        try:
            # now try complex volume
            Ms_cpx_vol = Ms.complex_volume(verified_modulo_2_torsion=True, bits_prec = prec)
            Mt_cpx_vol = Mt.complex_volume(verified_modulo_2_torsion=True, bits_prec = prec)
            diff = Ms_cpx_vol - Mt_cpx_vol
            # since we are here, the real part of diff is basically zero.
            # We check that:
            RIF = diff.real().parent()
            eps = RIF(2**-(prec/2)) 
            assert -eps < diff.real() < eps

            # The imaginary part is, up to scale, the CS
            # invariant.  However, it is only defined up to adding
            # copies of i*pi^2/2.  So we need to show that the
            # difference is not close to a multiple of i*pi^2/2.
            diff = diff.imag()
            RIF = diff.parent()
            Pi = RIF(pi)
            multiple = Pi**2 / 2
            ratio = diff / multiple
            frac = ratio - ratio.floor()
            if eps < frac < 1 - eps: 
                verbose_print(verbose, 6, [M, s, t, 'verified complex volume distinguishes at precision', prec])
                return True
            else:
                verbose_print(verbose, 6, [M, s, t, 'complex volumes very close at precision', prec])
        except Exception as e:
            verbose_print(verbose, 6, [M, s, t, "failed to compute complex volume at precision", prec, str(e)])
        
            # Let us not randomize, since we already have a good triangulation...

    # Length spectra are slow, but worth trying in a pinch
    # We creep up on higher and higher length cutoffs
    
    cutoff = 1.0
    step = 0.2
    for i in range(tries):
        if are_distinguished_by_length_spectrum(Ms, Mt, tries=tries, cutoff = cutoff, verbose=verbose):
            return True
        cutoff += step
        
    return False
    
