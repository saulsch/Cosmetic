#
# geom_tests.py
#

# This file contains utility code that applies various topological and geometric tests
# for dealing with slopes and determining the geometric type of the filling. It also
# contains code for distinguishing two fillings from one another using geometry.
# The main organizing principle is: routines land here if they use geometry or
# geometrization. Routines also land here if they are needed for both knot complements
# and general cusped manifolds.
#
# Fundamental group routines are not here -- they are in fundamental.py .

import snappy
import regina
import dunfield
import fundamental

from verbose import verbose_print

# Math 

from sage.functions.log import exp
from sage.functions.other import sqrt, ceil, floor
from sage.arith.misc import gcd, xgcd, factor
from sage.symbolic.constants import pi
from sage.symbolic.ring import SR
from sage.modules.free_module_element import vector

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


# sanity check


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


def a_shortest_lattice_point_on_line(point, direction, m, l):
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
    rounded_part = real_part.round() # not the floor, not the ceiling...
    left, right = rounded_part.endpoints()
    # if left and right are separated (say, because real_part contains
    # a half integer) we could give up, but instead:
    # Old: assert 0.0 <= right - left < 0.1 
    k = int(left)
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


def cusp_invariants(M):
    """
    Given a snappy manifold with one cusp, returns the holonomies of
    the current meridian and longitude, and also the square root of
    the area.
    """
    # Note - this uses the current framing, whatever it is
    [(m,l)] = M.cusp_translations(verified = True, bits_prec = 200)
    norm_fac = sqrt(l * m.imag())
    return m, l, norm_fac


# Get a list of short slopes


def find_short_slopes(M, len_cutoff, normalized=False, verbose=3):
    """
    Given a one-cusped hyperbolic manifold M and a length cutoff len_cutoff,
    find all slopes on the cusp that are shorter than len_cutoff.
    The Boolean flag 'normalized' clarifies whether the length cutoff is normalized
    (in the sense of Hodgson-Kerckhoff). If true, we convert to un-normalized,
    geometric length.
    The routine accepts M with an arbitrary framing, installs the geometric
    framing on a copy N to do its work, and returns slopes in the original coordinates.
    """
    verbose_print(verbose, 12, [M, 'entering find_short_slopes'])

    name = M.name()
    N = M.copy()

    # Fix the framing on the copy N to be shortest
    cob = N.set_peripheral_curves('shortest', return_matrices = True)
    # but remember the original meridian and longitude.
    meridian = cob[0][0]
    longitude = cob[0][1]

    m, l, norm_fac = cusp_invariants(N)
    if normalized==False:
        cutoff = len_cutoff
    else:
        cutoff = len_cutoff * norm_fac
    
    p_max = int(ceil(cutoff/abs(m)).endpoints()[0])
    q_max = int(ceil(cutoff/abs(l)).endpoints()[0])
    verbose_print(verbose, 10, [name, 'maximal m coeff', p_max, 'merid length', abs(m).endpoints()[0]])
    verbose_print(verbose, 10, [name, 'maximal l coeff', q_max, 'long length', abs(l).endpoints()[0]])

    # get the short slopes in the geometric framing
    slopes = []
    for p in range(0, p_max + 1): # do not need neg p as (p,q) = (-p,-q) is preserved by framing change
        for q in range(-q_max, q_max + 1):
            if gcd(p, q) == 1 and abs(p*m + q*l) <= cutoff:    
                slopes.append((p,q))
                
    verbose_print(verbose, 12, ['In geometric framing:', slopes])

    # convert the short slopes to the original framing
    slopes_converted = set( preferred_rep((alg_int(s, longitude), alg_int(meridian, s))) for s in slopes )
    verbose_print(verbose, 5, [name, len(slopes_converted), 'slopes shorter than', cutoff])
    verbose_print(verbose, 10, ['In original framing:', slopes_converted])
    
    return slopes_converted


# systole


def systole_with_covers(M, tries=10, verbose=3):
    """
    Given a snappy Manifold M,
    try to compute a lower bound for the systole.
    If direct computation fails, then try taking covers.
    The idea is that the systole of M is at least (1/n) times
    the systole of an n-fold cover.
    We only care about systoles that are shorter than 0.15.
    """
    
    name = M.name()
    verbose_print(verbose, 12, [name, "entering systole_with_covers"])

    retriang_attempts = 2*tries
    # This is a hack. In our context, tries is at most 8. But here, we want 
    # to retriangulate many times, until we succeed.


    for deg in range(1, 6):
        cov = M.covers(deg)
        for N in cov: 
            for i in range(retriang_attempts): # that looks like a magic number... 
                for j in range(i):
                    N.randomize()
                try:
                    # Q = N.copy()
                    sys = systole(N, verbose = verbose)
                    verbose_print(verbose, 10, ['systole of', deg, 'fold cover', N, 'is at least', sys])
                    return (sys/deg)
                except:
                    sys = None
                    verbose_print(verbose, 10, [N, 'systole failed on attempt', i])



def systole(M, verbose = 3):
    """
    Given a snappy Manifold M,
    tries to compute the systole of M, non-rigorously (for now).
    We only care about systoles that are shorter than 0.15.
    """
    name = M.name()
    N = M.high_precision()
    verbose_print(verbose, 12, [name, "entering systole"])
    spec = N.length_spectrum(0.15, full_rigor = True) # Ok - what does 'full-rigor' actually mean?
    verbose_print(verbose, 12, [name, "computed length spectrum"])
    if spec == []:
        return 0.15 # any systole larger than this gets ignored. 
    else:
        return spec[0].length.real()


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
    N = M.copy()
    r=(1,0)
    N.dehn_fill(r)
    exceptional, type_except = fundamental.is_exceptional_due_to_fundamental_group(N, tries, verbose)
    if type_except=='S3':
        verbose_print(verbose, 5, ['Lucky guess:', M, r, 'has trivial fundamental group'])
        is_knot = True
        return r, is_knot, geometrically_easy, regina_easy

    # Now, try using geometry
    M = dunfield.find_positive_triangulation(M, tries, verbose)
    
    if M.solution_type() != 'all tetrahedra positively oriented':
        verbose_print(verbose, 10, ['Bad triangulation:', M.name(), M.solution_type()])
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
        N = M.copy()
        N.dehn_fill(r)

        # Fundamental group
        
        exceptional, type_except = fundamental.is_exceptional_due_to_fundamental_group(N, tries, verbose)
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
        N = M.copy()
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
    # m, l, _ = cusp_invariants(M) [or geom_tests.cusp_invariants(M)]
    # Computing cusp_invariants(M) is slow, so we do not do it here.
    #
    # It is not clear that we should bother with the six-theorem
    if abs(p*m + q*l) > 6: # six-theorem
        return True            

    N = M.copy()
    N.dehn_fill(s)

    for i in range(tries):
        for j in range(i+1):
            if i > 0:
                N.randomize()
            is_except, _ = fundamental.is_exceptional_due_to_fundamental_group(N, 3, verbose)
            if is_except:
                return False
        for j in range(1): # this is not a typo,
            # because Nathan iterates and randomizes for us
            if dunfield.is_hyperbolic(N, i+1, verbose): 
                return True
        if i > 0: # gosh, this is a tricky one... so
            if is_toroidal_wrapper(N, verbose)[0]:
                return False 
            if is_reducible_wrapper(N, tries, verbose)[0]:
                return False 
            name = dunfield.regina_name(N)
            if name[:3] == 'SFS': # We trust the regina_name.
                return False
    return None


# Dealing with a pair of slopes


def is_distinguished_by_length_spectrum(M, s, t, check_chiral=False, cutoff = 3.1, verbose=5):
    """
    Given a cusped manifold M and two slopes (where we think that both
    fillings are hyperbolic), try to distinguish M(s) from M(t) using the 
    complex length spectra.
    
    If check_chiral==False, then we only check for orientation-preserving
    isometries.
    
    If check_chiral==True, then we check for both orientation-preserving and
    orientation-reversing isometries.
    
    The cutoff variable determines how far into the length spectrum we bother checking.
    To save computer time, we creep up on the cutoff rather than jumping straight there.
    
    Returns True if the manifolds are distinguished, and False if not. 
    A True answer is only as rigorous as the length spectrum (so, not entirely).
    """
    name = M.name()
    verbose_print(verbose, 12, [name, s, t, 'entering is_distinguished_by_length_spectrum'])
    Ms = M.high_precision()
    Mt = M.high_precision()
    
    Ms.dehn_fill(s)
    Mt.dehn_fill(t)
    try:
        Ms_domain = Ms.dirichlet_domain()
        Mt_domain = Mt.dirichlet_domain()
    except Exception as e:
        verbose_print(verbose, 6, [M, s, t, e])

    length_step = 0.2
    current_length = min(1.0, cutoff)
    
    norm_cutoff = 0.1 # If vector norms differ by this much, the vectors really are different
    
    while current_length <= cutoff:
        # Compute length spectra without multiplicity
        Ms_spec = Ms_domain.length_spectrum_dicts(current_length, grouped = False)
        Mt_spec = Mt_domain.length_spectrum_dicts(current_length, grouped = False)
        # Throw away all but the complex lengths
        Ms_spec = [line.length for line in Ms_spec]
        Mt_spec = [line.length for line in Mt_spec]
        
        minlen = min(len(Ms_spec), len(Mt_spec))
        
        M_diff = [Ms_spec[i] - Mt_spec[i] for i in range(minlen)]
        M_norm = vector(M_diff).norm()
        
        M_conjdiff = [Ms_spec[i] - Mt_spec[i].conjugate() for i in range(minlen)]
        M_conjnorm = vector(M_conjdiff).norm()
        
        if not(check_chiral) and M_norm > norm_cutoff:
            verbose_print(verbose, 6, [M, s, t, 'length spectrum up to', current_length, 'distinguishes oriented manifolds'])
            return True
        if check_chiral and M_norm > norm_cutoff and M_conjnorm > norm_cutoff:
            verbose_print(verbose, 6, [M, s, t, 'length spectrum up to', current_length, 'distinguishes un-oriented manifolds'])
            return True
        else:
            verbose_print(verbose, 10, [M, s, t, 'length spectrum up to', current_length, 'fails to distinguish'])
        current_length += length_step
            
    return False


def is_distinguished_by_hyp_invars(M, s, t, tries, verbose):
    """
    Given a cusped manifold M and two slopes (where we think that both
    fillings are hyperbolic), try to prove that M(s) is not
    orientation-preservingly homeomorphic to M(t). 
    Returns a tuple of booleans (distinguished, rigor)
    distinguished is True if we can tell the manifolds apart.
    rigor is True if we did so using rigorous verified invariants.
    """
    name = M.name()
    verbose_print(verbose, 12, [name, s, t, 'entering is_distinguished_by_hyp_invars'])
    Ms = M.copy()
    Mt = M.copy()
    
    Ms.chern_simons() # must initialise - see docs
    Mt.chern_simons()
    Ms.dehn_fill(s)
    Mt.dehn_fill(t)
    Ms = dunfield.find_positive_triangulation(Ms, tries) 
    Mt = dunfield.find_positive_triangulation(Mt, tries)

    if Ms == None or Mt == None:
        verbose_print(verbose, 6, [M, s, t, 'positive triangulation fail'])
        return (None, None)
    
    prec = 40 # note the magic number 40.  Fix.
    rigor = True
    for i in range(tries):
        prec = prec * 2

        try:
            # Try ordinary volume first
            Ms_vol = Ms.volume(verified=True, bits_prec = prec)
            Mt_vol = Mt.volume(verified=True, bits_prec = prec)

            if abs(Ms_vol - Mt_vol) > 4* (1/2)**prec:
                verbose_print(verbose, 6, [M, s, t, 'verified volume distinguishes at precision', prec])
                return (True, rigor)
            else:
                verbose_print(verbose, 6, [M, s, t, 'volumes very close at precision', prec])
        except Exception as e:
            verbose_print(verbose, 6, [M, s, t, e])
            
        try:
            # Now, try complex volume, ie, Vol + i*CS
            Ms_cpx_vol = Ms.complex_volume(verified_modulo_2_torsion=True, bits_prec = prec)
            Mt_cpx_vol = Mt.complex_volume(verified_modulo_2_torsion=True, bits_prec = prec)

            if abs(Ms_cpx_vol - Mt_cpx_vol) > 4* (1/2)**prec:
                verbose_print(verbose, 6, [M, s, t, 'verified complex volume distinguishes at precision', prec])
                return (True, rigor)
            else:
                verbose_print(verbose, 6, [M, s, t, 'complex volumes very close at precision', prec])
        except Exception as e:
            verbose_print(verbose, 6, [M, s, t, e])
        
            # Let us not randomize, since we already have a good triangulation...

    rigor = False
    if is_distinguished_by_length_spectrum(M, s, t, cutoff = 1.1, verbose=verbose):
        return (True, rigor)
    else:
        return (False, None)
    
    '''
    for i in range(tries):
        try:
            # Now, try the bottom of the length spectrum.
            # Note: "full rigor" isn't. This is NOT rigorous.
            Ms_spec = Ms.length_spectrum(full_rigor=True)
            Mt_spec = Mt.length_spectrum(full_rigor=True)

            if len(Ms_spec) > 0 and len(Mt_spec) > 0:
                # let's be careful to avoid handedness issues
                ms = Ms_spec[0].length.real()
                mt = Mt_spec[0].length.real()
                if abs(ms - mt) > 0.1: 
                    verbose_print(verbose, 0, [M, s, t, "bottom of length spectrum distinguishes"])
                    return (True, rigor)

            Ms_multi = [a.multiplicity for a in Ms.length_spectrum(2, full_rigor=True)]
            Mt_multi = [a.multiplicity for a in Mt.length_spectrum(2, full_rigor=True)]

            if Ms_multi != Mt_multi:
                verbose_print(verbose, 0, [M, s, t, "bottom of multiplicity spectrum distinguishes"])
                return (True, rigor)

        except Exception as e:
            verbose_print(verbose, 6, [M, s, t, e])

    return (False, None)
    '''
