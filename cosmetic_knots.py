#
# cosmetic_knots.py
#

# Goal - rule out cosmetic surgeries on various knots in S^3. 

import snappy
import spherogram
import regina
import dunfield
import geom_tests as gt
import regina_tests as rt


# from tqft import Jones_tests
from verbose import verbose_print

# Math
from sage.functions.other import sqrt, ceil, floor
from sage.symbolic.constants import pi
from sage.arith.misc import gcd
from sage.symbolic.ring import SR
from sage.rings.number_field.number_field import CyclotomicField

from string import ascii_letters


# IO

def get_knots_from_file(filename, header=True):
    """
    Given a CSV file (eg, from regina), read the file and return the list of lines.
    If header==True, remove the header line.
    """
    f = open(filename, "r")
    data = f.readlines()
    if header:
        data = data[1:]
    data = [line.strip() for line in data]
    data = [line for line in data if line != ""]
    f.close()
    return data

def full_dt(short_dt):
    """
    Given short DT code, as in Regina,
    build and return the full DT code in snappy notation.
    """
    p = ascii_letters[len(short_dt) - 1]
    full_dt_code = "DT:" + p + "a" + p + short_dt
    return full_dt_code

def get_DTs_from_regina(filename):
    """
    Given a csv file from regina, return the list of DT codes in
    snappy notation.  CSV files can be found here:
    https://regina-normal.github.io/data.html
    """
    data = get_knots_from_file(filename, header=True)

    DT_codes = []
    for line in data:
        stuff = line.split(",")
        DT_codes.append(full_dt(stuff[2]))
    return DT_codes


# Extracting a link from a manifold, and vice versa


def link_from_manifold(M, verbose = 3):
    """
    Given a snappy manifold M, try to extract the associated link K
    Return K if successful, or None otherwise.  Part of the point of
    the function is error trapping: snappy crashes if no link is
    found, but we do not want to crash.
    """
    try:
        K = M.link()  # get the underlying knot or link
        return K
    except ValueError:
        pass
    verbose_print(verbose, 3, [M.name(), 'could not get link via M.link()'])
    
    names = M.identify()
    for name in names:
        try:
            K = name.link()
            return K
        except ValueError:
            pass
    verbose_print(verbose, 3, [M.name(), 'could not get link via M.identify()'])

    ### FIX - TODO - HERE - BROKEN - 2023-12-19
    
    try:
        K = M.exterior_to_link()
        return K
    except:
        pass
            
    if K == None:
        verbose_print(verbose, 3, [M.name(), 'could not get link'])

    # TODO: Perhaps try to retriangulate, using tries
    return K


def name_manifold_and_link(in_obj, verbose=3):
    """
    Given in_obj, which is either a snappy Manifold, a spherogram Link, or
    a string containing a name, return all three objects: the name,
    the manifold, and the link.
    """        
    if type(in_obj) is snappy.Manifold:
        M = in_obj
        name = M.name()
        K = link_from_manifold(M, verbose)
        verbose_print(verbose, 10, [name, 'Received as manifold'])
    if type(in_obj) is spherogram.links.invariants.Link:
        K = in_obj
        M = K.exterior()
        name = K.DT_code(DT_alpha=True)
        verbose_print(verbose, 10, [name, 'Received as link'])
    if type(in_obj) == str:
        name = in_obj
        verbose_print(verbose, 10, [name, 'Received as string'])
        if name[:2] == 'DT' or name[:2] == 'dt':  # We received a DT code
            K = snappy.Link(name)
            M = K.exterior()
        else:
            M = snappy.Manifold(name)
            K = link_from_manifold(M, verbose)
    return name, M, K


# Framing issues


def fix_framing(M):
    """
    Given a knot complement M, set the peripheral curves to be the homological
    meridian and longitude. This alters M and returns the change of basis matrix.
    """    
    meridian, _, _, _ = gt.get_S3_slope_hyp(M)
    assert meridian is not None
    # If get_S3_slope fails, we should complain. Right now, it is in there as an assert.
    longitude = M.homological_longitude()
    sign = gt.alg_int(meridian, longitude)
    assert sign == 1 or sign == -1
    meridian = (sign*a for a in meridian)
    cob = M.set_peripheral_curves([meridian, longitude])
    return cob
    

# Alexander polynomial and related invariants

def genus_lower_bound(M, verbose=3):
    """
    Computes a lower bound on knot genus, via span of Alexander polynomial.
    """
    P = M.alexander_polynomial()
    verbose_print(verbose, 10, [P, 'Alexander polynomial'])
    return P.degree()/2

def Alexander_tests(knot, name, verbose=3):
    """
    Accepts either a snappy Link or a snappy Manifold.
    Computes Alexander polynomial, Casson invariant, and genus lower bound.
    These invariants are computed as a package, so that we only compute the polynomial once.
    """

    if knot == None:
        return None, None

    if type(knot) is snappy.Manifold:
        verbose_print(verbose, 8, [name, 'Computing Alexander polynomial from manifold'])
    if type(knot) is spherogram.links.invariants.Link:
        verbose_print(verbose, 8, [name, 'Computing Alexander polynomial from knot diagram'])

    P = knot.alexander_polynomial()
    verbose_print(verbose, 10, [name, P, 'Alexander polynomial'])
    deg = P.degree()/2
    verbose_print(verbose, 10, [deg, 'half the span'])
    
    Rin = P.parent()  # the polynomial ring where P lives
    # normalize the polynomial so that positive and negative powers match and
    # so that it evaluates to 1 at 1
    Q = P/(Rin.gen()**deg * P(1))  
    verbose_print(verbose, 10, [Q, 'Normalized Alexander polynomial'])
    assert Q(1) == 1
    A = Q.derivative().derivative()
    verbose_print(verbose, 10, [A, 'second derivative'])
    return Q, int(A(1)/2), int(deg)

# Turaev genus of a diagram

def merge(lsts):
    """
    This function takes a list of lists and merges any subsets that have 
    overlapping elements.  Written by Adam Lowrance.
    """
    out = []
    while len(lsts) > 0:
        # splits lsts into the first element and the rest
        first, *rest = lsts
        # turns first into a set
        first = set(first)
        # Make sure we enter the while loop
        lf = -1
        while len(first) > lf:
            # this ensures we stay in the while loop as long as first gets longer
            lf = len(first)

            rest2 = []
            for r in rest:
                # check to see if there is an element in common between first and r
                if len(first.intersection(set(r))) > 0:
                    # if there is an element in common, take the union of first and r
                    first |= set(r)
                else:
                    # if there is no element in common, save r for later use
                    rest2.append(r)
            # After we've saved all the different r's that don't intersect first, rename them as rest
            rest = rest2
        # We've found everything that intersects with first, so save it
        out.append(first)
        lsts = rest
    return out


def turaev_genus(pd_code):
    '''
    Given the PD code of a (connected) diagram, return the genus of the associated 
    Turaev surface. This is an upper bound on the Turaev genus of the link.
    Written by Adam Lowrance
    '''
    # Split each crossing in the pd_code into A-resolutions and B-resolutions
    a_resolutions =[]
    b_resolutions =[]
    for i in range(len(pd_code)):
        a_resolutions.append([pd_code[i][0],pd_code[i][1]])
        a_resolutions.append([pd_code[i][2],pd_code[i][3]])
        b_resolutions.append([pd_code[i][0],pd_code[i][3]])
        b_resolutions.append([pd_code[i][1],pd_code[i][2]])
    # Use the merge function to create the all-A and all-B states
    all_a_state = merge(a_resolutions)
    all_b_state = merge(b_resolutions)
    # The Turaev genus of D is 1/2(2 + c(D) - s_A(D) - s_B(D)).
    # The number of crossings c(D) is the length of pd_code.
    # The number of components s_A(D) of the all-A state is len(all_a_state)
    # The number of components s_B(D) of the all-B-state is len(all_b_state)
    # Return the Turaev genus of D.
    return int((2 + len(pd_code)-len(all_a_state)-len(all_b_state))/2)


def thickness_upper_bound(K, name, verbose=3):
    '''
    Given a snappy knot K and a name (for bookkeeping),
    returns a cheap upper bound on th(K), the Heegaard Floer thickness of K.
    We use Lowrance's theorem: th(K) <= g_T(K), where g_T(K) is Turaev genus.
    We get an upper bound on g_T(K) by computing the Turaev genus of the diagram.
    A very cheap upper bound is: g_T(K) <= c(K)/2, where c(K) is crossing number.
    We compute this, but do not return it.
    '''
    
    if K == None:
        return None
    crossing_num = len(K.crossings)
    
    if K.is_alternating():
        turaev_bound = 0
    else:
        pd_code = K.PD_code()
        turaev_bound = turaev_genus(pd_code)
    assert 2*turaev_bound <= crossing_num
    
    verbose_print(verbose, 10, [name, crossing_num, 'crossings,', turaev_bound, 'Turaev genus'])
    
    return turaev_bound


# Jones polynomial and related invariants

def Jones_tests(K, name, verbose=3):
    """
    Given a snappy link K and its name, compute the Jones polynomial
    V(K), in the original normalization. Then, return the following data:
    * V'''(1), the Ichihara-Wu invariant
    * (V'''(1)+3*V''(1))/-36, the Ito invariant (times four)
    * V(exp(2*Pi*I/5)), the Detcherry invariant  
    * c(K) - span(V(K)), an upper bound on the Turaev genus g_T(K)
    
    All of these are relevant to obstructing cosmetic surgeries.
    """
    
    if K == None:
        return None, None
        
    V = K.jones_polynomial(new_convention=False)
    # The 'new_convention=False' ensures we get classical Jones polynomial
    verbose_print(verbose, 10, [name, V, "Jones polynomial"])
    P = V.derivative().derivative() # Second derivative
    Q = V.derivative().derivative().derivative() # Third derivative
    
    Ito = int((Q(1)+3*P(1))/(-36)) # 4 times Ito's invariant v_3
    IchiharaWu = int(Q(1)) # Ichihara-Wu invariant
    
    w = CyclotomicField(5).gen() # so w = exp(2*Pi*I/5)
    Detcherry = V(w)
    
    cross = len(K.crossings) # crossing number of the given diagram
    Vspan = max(V.exponents()) - min(V.exponents())
    Turaev = cross - Vspan

    verbose_print(verbose, 10, [IchiharaWu, "Jones third derivative at 1"])
    verbose_print(verbose, 10, [Ito, "Four times Ito invariant v_3"])
    verbose_print(verbose, 10, [Detcherry, "Jones poly evaluated at exp(2*Pi*I/5)"])
    verbose_print(verbose, 10, [Turaev, "upper bound on Turaev genus from span(Jones)"])
    
    return IchiharaWu, Ito, Detcherry, Turaev


# Knot Floer homology and related invariants

def HFK_thickness(HFK):
    '''
    Given a dictionary HFK, as in the output of K.knot_floer_homology(),
    compute the minimum and maximum delta-grading. The difference between
    the minumum and maximum is the thickness.
    '''
    gradings = []
    for r in HFK['ranks']:
        g = r[1]-r[0] # The delta-grading of the group at position r
        if g not in gradings:
            gradings.append(g)
    thickness = max(gradings)-min(gradings)
    return thickness

def HFK_tests(K, name, verbose=3):
    '''
    Given a snappy knot K, and its name (for bookkeeping), uses 
    Szabo's algorithm to compute the knot Floer homology of K.
    Returns three invariants that obstruct cosmetic surgeries:
    * the tau invariant
    * the Seifert genus of K
    * the thickness of K
    '''
    
    if K == None:
        return None, None, None
    
    HFK = K.knot_floer_homology()
    tau = HFK['tau']
    genus = HFK['seifert_genus']
    thickness = HFK_thickness(HFK)

    # Sanity checks - can be commented out once we verify on large sample
    # assert genus >= genus_lower_bound(M, verbose)
    # verbose_print(verbose, 20, [thickness, thickness_upper_bound(K, name, verbose)])
    # assert thickness <= thickness_upper_bound(K, name, verbose)
    
    verbose_print(verbose, 12, ['HFK:', HFK])
    verbose_print(verbose, 10, [genus, 'Seifert genus,', tau, 'Tau invariant,', thickness, 'HFK thickness'])
    
    return tau, genus, thickness 
    # We should also return epsilon


def Hanselman_slopes(K, name, use_HFK=True, verbose=3):
    """
    Given a snappy knot K and its name (for bookkeeping)
    use Hanselman's Theorem 2 to compute a list of (possibly)
    cosmetic slopes to check. Return the list.
    
    The flag use_HFK determines whether we compute the knot
    Floer homology of K or simply rely on bounds coming from
    the Alexander polynomial and Turaev genus.
    """

    if use_HFK==True:
        _, g, th = HFK_tests(K, name, verbose)
    else:
        M = K.exterior()
        g = max(2, genus_lower_bound(M, verbose))
        # We may always use g>=2 in Hanselman's functions
        th = thickness_upper_bound(K, name, verbose)

    if th==None:
        # We could not compute thickness, possibly because K==None
        verbose_print(verbose, 3, [name, 'could not compute/estimate HFK thickness'])
        return None
            
    slopes = set()
    if g==2:
        slopes.add((2,1))
    if g>=2:
        Hanselman_bound = int( (th + 2*g)/(2*g*(g-1)) )
        for q in range(1, Hanselman_bound+1):
            slopes.add((1,q))
    
    if use_HFK==True and verbose > 5:
        print(name, 'Hanselman slopes using HFK', slopes)
    if use_HFK==False and verbose > 5:
        print(name, 'Hanselman slopes using estimates', slopes)
    
    return slopes


# routines for checking things on a knot complement
            
def check_knot_cosmetic_slope(M, s, m, l, tries, verbose):
    '''
    Given a knot in S^3 with the homological framing, and a slope s,
    decides if s and sn (the negative slope) are possibly a cosmetic
    pair.  If they are not, returns None. 
    If they are (possibly) cosmetic, return the reason why they might be.  
    References:
    [Ni-Wu, "Cosmetic surgeries on knots in S3"]
    [Ravelomanana, "Exceptional Cosmetic surgeries on S3"]
    [Futer-Purcell-Schleimer, "Effective Bilipschitz Bounds on Drilling and Filling"] 
    '''
    verbose_print(verbose, 12, [M, s, 'entering check_knot_cosmetic_slope'])

    sn = (s[0], -s[1])
    # if s and sn are parallel, skip
    if gt.alg_int(s, sn) == 0:
        verbose_print(verbose, 12, [M, s, sn, 'are parallel'])
        return None

    s_hyp = gt.is_hyperbolic_filling(M, s, m, l, tries, verbose)
    sn_hyp = gt.is_hyperbolic_filling(M, sn, m, l, tries, verbose)

    if s_hyp == None:
        verbose_print(verbose, 6, [M, s, 'could not determine type'])
    if sn_hyp == None:
        verbose_print(verbose, 6, [M, sn, 'could not determine type'])
    if s_hyp == None or sn_hyp == None:
        verbose_print(verbose, 6, [M, s, sn, 'one of them is not recognized as hyp or except'])
        return (M.name(), s, sn, 'one of them is not recognized as hyp or except')

    if (s_hyp and not sn_hyp) or (not s_hyp and sn_hyp):
        verbose_print(verbose, 6, [M, s, sn, 'only one is hyperbolic'])
        return None
    elif (s_hyp and sn_hyp):
        verbose_print(verbose, 6, [M, s, sn, 'both hyperbolic'])
        if gt.are_distinguished_by_hyp_invars(M, s, sn, tries, verbose)
            return None
        return (M.name(), s, sn, 'unable to distinguish')
    else:
        assert( not s_hyp and not sn_hyp ) 
        if not( gt.preferred_rep(s) == (1,1) or gt.preferred_rep(s) == (1,-1) ):
            verbose_print(verbose, 6, [M, s, sn, 'exceptionals distinguished by Ravelomanana'])
            return None
        else:
            P = snappy.Manifold(M)
            Pn = snappy.Manifold(M)
            P.dehn_fill(s)
            Pn.dehn_fill(sn)
            out = rt.torus_decomp_wrapper(P, tries, verbose)
            outn = rt.torus_decomp_wrapper(Pn, tries, verbose)
            if out[0] != outn[0]:
                verbose_print(verbose, 2, [M, s, sn, 'exceptionals distinguished by Regina: only one is toroidal'])
                return None
            elif not out[0] or not outn[0]:
                # At least one of the fillings is atoroidal
                verbose_print(verbose, 2, [M, s, sn, 'exceptionals distinguished by Regina and Ravelomanana'])
                return None
            else:
                verbose_print(verbose, 0, [M, s, sn, out, outn, 'toroidal manifolds -- examine the pieces'])
                return (M.name(), s, sn, 'toroidal manifolds '+str(out[1])+', '+str(outn[1]))


def systole_short_slopes(M, tries=10, verbose=3):
    '''
    Given a knot complement M, presumed to be hyperbolic and equipped with
    the homological framing, compute the systole and use it to build a list of short
    slopes. 
    
    References: Thm 1.10 of EffectiveBilipschitz, plus strengthened theorem (currently 
    Thm 3.1) of the CosmeticByComputer paper.
    '''
    
    sys = gt.verified_systole_with_drilling(M, cutoff=0.15, tries=tries, verbose=verbose)
    if sys == None:
        return None

    # get the translation lengths and the normalisation factor and bounds on p and q
    verbose_print(verbose, 2, [M, 'systole is at least', sys])
    norm_len_cutoff = max(9.97, sqrt((2*pi/sys) + 56.0)) 
    verbose_print(verbose, 4, [M, 'norm_len_cutoff', norm_len_cutoff])
    
    # Build list of short slopes in the homological framing. Note that the list we
    # receive from find_short_slopes is already in preferred_rep form.
    short_slopes_all = gt.find_short_slopes(M, norm_len_cutoff, normalized=True, verbose=verbose)
    verbose_print(verbose, 4, [M, len(short_slopes_all), 'short slopes found'])
    verbose_print(verbose, 10, [short_slopes_all])

    # remove duplicate slopes, meridian, and longitude.
    short_slopes = set()
    for s in short_slopes_all:
        p = s[0]
        q = s[1]
        if p == 0 or q ==0: 
            # No need to check (0,1) or (1,0) slopes - they cannot be cosmetic
            # by Gordon-Luecke and homology.
            continue
        if gt.preferred_rep((s[0], -s[1])) not in short_slopes:
            # That is, we have not yet added the negative of this slope
            verbose_print(verbose, 10, [M, s, 'adding to list of short slopes to check'])
            short_slopes.add(gt.preferred_rep(s))
    verbose_print(verbose, 2, [M, len(short_slopes), 'short slopes left after pruning'])
    verbose_print(verbose, 4, [short_slopes])
    return short_slopes

def check_knot_cosmetic(knot, use_HFK = True, tries=10, verbose=3):
    '''
    Given a knot complement in S^3, install the homological framing on M
    and then check a list of slopes for being possibly a cosmetic pair.

    The flag 'use_HFK' what theorems are used form a list of slopes to check.
    If use_HFK == True, we apply the theorems of Hanselman and Daemi-Lidman-Miller Eismeier, 
    which says that the only potentially cosmemtic surgery pair is (2,1) and (2,-1).
    If use_HFK == False, we check all slopes that are shorter than a normalized length cutoff,
    determined by the systole as in FPS theorem. Each (p,q) slope is compared to (p,-q).
        
    We do *not* pre-screen M using knot invariants. That pre-screening should
    happen in prune_using_invariants(...) instead.
    '''
    
    # Let's be liberal in what we accept
    name, M, K = name_manifold_and_link(knot, verbose=verbose)

    # But not too liberal
    assert gt.is_knot_manifold(M)
    # Install the homological framing on M.
    cob = fix_framing(M)
    
    hom_slopes = None
    short_slopes = None
    
    if use_HFK == True:
        slopes = set()
        slopes.add((2,1))

    # From now on, we need geometry. Install a good hyperbolic metric,
    # or give up if we cannot find one.
    
    mfd, reason = gt.sanity_check_cusped(M, tries=tries, verbose=verbose)
    if mfd == None:
        # We did not find a hyperbolic structure
        if reason == 'is a torus knot':
            # M is a torus knot, so it has non-zero tau invariant, and
            # so by Ni-Wu satisfies the cosmetic surgery conjecture
            verbose_print(verbose, 3, [M, 'is a torus knot; no cosmetic surgeries by Ni-Wu'])
            # Note: torus knots should get caught by the Casson_invt test above, so we should
            # not end up in this branch.
            return []
        else:
            # M is some other non-hyperbolic manifold. Give up.
            return [(name, None, None, reason)]
    else:
        # We found a hyperbolic structure
        assert type(mfd) is snappy.Manifold
        assert mfd.solution_type() == 'all tetrahedra positively oriented'
        M = mfd
            
    m, l, norm_fac = gt.cusp_invariants(M, tries=tries, verbose=verbose)
    verbose_print(verbose, 5, [name, 'cusp_stuff', 'merid', m, 'long', l, 'norm_fac', norm_fac])

    if use_HFK == False:
        slopes = systole_short_slopes(M, tries, verbose)

    if slopes == None:
        verbose_print(verbose, 0, [M.name(), 'systole fail!'])
        return [(name, None, None, 'could not compute systole')]

    
    verbose_print(verbose, 3, [name, 'checking these slopes:', slopes])

    bad_uns = []

    for s in slopes:
        p = s[0]
        q = s[1]
        verbose_print(verbose, 20, [name, s, 'normalized slope length', abs(p*m + q*l)/norm_fac])
        reason = check_knot_cosmetic_slope(M, s, m, l, tries, verbose)
        if reason is not None:
            verbose_print(verbose, 2, [reason])
            bad_uns.append(reason)
    verbose_print(verbose, 3, [name, 'finished'])
    verbose_print(verbose, 0, bad_uns)
    return bad_uns



def prune_using_invariants(knots, Alexander=True, Casson=True, Genus_thick_quick=True, Jones_deriv=True, Jones_fifth=True, Tau_test=True, Hanselman_HFK=True, verbose=3, report=100):
    '''
    Given a list of knots or knot complements, tries to
    rule out cosmetic surgeries using the followifng tests:
    * Daemi-Lidman-Miller Eismeier test (Alexander polynomial)
    * Boyer-Lines test (second derivative of Alexander polynomial at 1) 
    * Quick genus-thickness test (span(Alexander) and Turaev genus)
    * Ichihara-Wu test (third derivative of Jones polynomial at 1)
    * Detcherry test (Jones polynomial at 5th root of 1) 
    * Ni-Wu test (tau invariant)
    * HFK Hanselman test (exact genus and HFK thickness)

    The tests are ordered according to speed, for a typical non-alternating knot. 
    
    Returns a list of only those knots for which  these tests do not succeed. 
    The remaining knots would have to be checked using hyperbolic methods.
    '''

    bad_uns = []
    Alexander_ruled_out = 0
    Casson_ruled_out = 0
    Quick_GT_ruled_out = 0
    Jones_ruled_out = 0
    Detcherry_ruled_out = 0
    Tau_ruled_out = 0
    Hanselman_ruled_out = 0

    for n, knot in enumerate(knots):
        if verbose > 0 and n % report == 0:
            print('report', n, ':', Alexander_ruled_out, 'Ruled out by Alexander polynomial,', Casson_ruled_out, 'ruled out by Casson invariant,')
            print(Quick_GT_ruled_out, 'ruled out by quick genus-thickness test,', Jones_ruled_out, 'ruled out by Jones derivative,', Detcherry_ruled_out, 'ruled out by Jones 5th root of 1,')
            print(Tau_ruled_out, 'ruled out by tau invariant,', Hanselman_ruled_out, 'ruled out by HFK genus-thickness test')
            print('Last few difficult knots', bad_uns[-5:])

        # Be somewhat generous in what we accept
        name, M, K = name_manifold_and_link(knot, verbose=verbose)
        # We use K to compute all of the invariants.
        # The Alexander polynomial can be computed from the fundamental group (hence from M),
        # but this is slower for large examples.

        # Collect Alexander polynomial data. Use the knot if possible
        if Alexander or Casson or Genus_thick_quick: # if we need the Alexander polynomial
            if K != None:
                A, C, genus_bound = Alexander_tests(K, name, verbose=verbose)
            else:
                A, C, genus_bound = Alexander_tests(M, name, verbose=verbose)

        # Daemi-Lidman-Miller Eismeier test, nontriviality of the Alexander polynomial:
        if Alexander:
            if A != None and A != 1:
                verbose_print(verbose, 3, [name, 'has nontrivial Alexander poly, no cosmetic surgeries by Daemi-Lidman-Miller Eismeier'])
                Alexander_ruled_out = Alexander_ruled_out + 1
                continue            

        # Boyer-Lines test via Casson invt, second derivative of the Alexander polynomial
        if Casson:
            if C != None and C != 0:
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Boyer-Lines'])
                Casson_ruled_out = Casson_ruled_out + 1
                continue

        # Get a cheap upper bound on HFK thickness from Turaev genus
        if Genus_thick_quick or Jones_fifth:
            th = thickness_upper_bound(K, name, verbose)
        
        # Apply the quick genus-thickness test (Hanselman + Wang)
        # Hanselman's inequality below, namely 'th < 2*g*(g-2)', becomes harder 
        # to satisfy when th goes up and g goes down.
        # Consequently, it is safe to substitute a cheap lower bound on genus
        # (namely, span(Alexander)/2) and a cheap upper bound on thickness
        # (namely, the Turaev genus of the diagram).
        if Genus_thick_quick:
            g = genus_bound
            if g != None and th != None:
                verbose_print(verbose, 6, [name, 'quick genus-thickness test', th, 2*g*(g-2)])
                # Hanselman portion of the test
                if th < 2*g*(g-2):
                    # The above inequality is never true when g=0,1,2, because th >= 0.
                    # For g >= 2, it is equivalent to (th + 2*g)/(2*g*(g-1)) < 1, which is the
                    # criterion in Hanselman's Theorem 2.
                    verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by quick genus-thickness test'])
                    Quick_GT_ruled_out = Quick_GT_ruled_out + 1
                    continue
                # Wang portion of the test
                if th == 0 and g == 1: 
                    # These must be alternating knots of genus exactly 1
                    verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Wang for alternating knots'])
                    Quick_GT_ruled_out = Quick_GT_ruled_out + 1
                    continue

        # Compute the Jones polynomial plus related values, if needed
        if Jones_deriv or Jones_fifth:
            jones_data = Jones_tests(K, name, verbose)

        # Ichihara-Wu test, third derivative of the Jones polynomial
        if Jones_deriv:
            J = jones_data[0]  # Third derivative at 1
            if J != None and J != 0:
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Ichihara-Wu'])
                Jones_ruled_out = Jones_ruled_out + 1
                continue
        
        # Detcherry test, Jones polynomial at 5th root of 1. This needs to be combined
        # with previously computed upper bound on HFK thickness.
        if Jones_fifth:
            D = jones_data[2]  # V_K(zeta5)
            verbose_print(verbose, 6, [name, 'th(K) <=', th, ', V_K(zeta5) =', D])
            if (th != None and th < 16) and (D != None and D != 1):
                # See the proof of Corollary 1.5 in Detcherry's paper.
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Detcherry'])
                Detcherry_ruled_out = Detcherry_ruled_out + 1
                continue

        # Compute knot floer homology plus related numbers, if needed
        if Tau_test or Hanselman_HFK:
            tau, g, th = HFK_tests(K, name, verbose)
        
        # Ni-Wu test, tau invariant
        if Tau_test:
            if tau != None and tau != 0:
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Ni-Wu'])
                Tau_ruled_out = Tau_ruled_out + 1
                continue
            

        # Hanselman HFK test: use the real genus and thickness
        # This incorporates the Wang test of genus one knots
        if Hanselman_HFK and th != None and g != None:
            verbose_print(verbose, 6, [name, 'Full Hanselman test', th, 2*g*(g-2)])
            # Wang portion of the test
            if g == 1: 
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Wang'])
                Hanselman_ruled_out = Hanselman_ruled_out + 1
                continue
            if th < 2*g*(g-2):
                # The above inequality is never true when g=0,1,2, because th >= 0.
                # For g >= 2, it is equivalent to (th + 2*g)/(2*g*(g-1)) < 1, which is the
                # criterion in Hanselman's Theorem 2.
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Hanselman genus-thickness test'])
                Hanselman_ruled_out = Hanselman_ruled_out + 1
                continue

        # At this point, all the above tests have failed.
        bad_uns.append(name)
        
    if verbose > 0:
            print('report', n+1, ':', Alexander_ruled_out, 'Ruled out by Alexander polynomial,', Casson_ruled_out, 'ruled out by Casson invariant,')
            print(Quick_GT_ruled_out, 'ruled out by quick genus-thickness test,', Jones_ruled_out, 'ruled out by Jones derivative,', Detcherry_ruled_out, 'ruled out by Jones 5th root of 1,')
            print(Tau_ruled_out, 'ruled out by tau invariant,', Hanselman_ruled_out, 'ruled out by HFK genus-thickness test')
    return bad_uns



def check_knots(knots, use_HFK = True, tries=10, verbose=4, report=20):
    
    bad_uns = []
    for n, knot in enumerate(knots): 
        out = check_knot_cosmetic(knot, use_HFK, tries, verbose)
        bad_uns.extend(out)
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n, bad_uns])
    return bad_uns

