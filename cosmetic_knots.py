#
# cosmetic_knots.py
#

# Goal - rule out cosmetic surgeries on various knots in S^3. 

import snappy
import spherogram
import regina
import dunfield
import geom_tests

from verbose import verbose_print

# Math

from sage.functions.other import sqrt, ceil, floor
from sage.symbolic.constants import pi
from sage.arith.misc import gcd
from sage.symbolic.ring import SR
from sage.rings.number_field.number_field import CyclotomicField
# from sage.rings.universal_cyclotomic_field import UniversalCyclotomicField

from string import ascii_letters


# IO


def get_knots_from_file(filename):
    f = open(filename, "r")
    data = f.readlines()
    data = [line.strip() for line in data]
    data = [line for line in data if line != ""]
    f.close()
    return data

def get_DTs_from_regina(filename):
    """
    Given a csv file from regina, return the list of DT codes in
    snappy notation.  CSV files can be found here:
    https://regina-normal.github.io/data.html
    """
    f = open(filename, "r")
    data = f.readlines()
    data = data[1:]
    data = [line.strip() for line in data]
    data = [line for line in data if line != ""]
    f.close()

    DT_codes = []
    for line in data:
        stuff = line.split(",")
        short_dt = stuff[2]
        p = ascii_letters[len(short_dt) - 1]
        full_dt = "DT:" + p + "a" + p + short_dt
        DT_codes.append(full_dt)
    return DT_codes


# Extracting a link from a manifold, and vice versa


def link_from_manifold(M, verbose=3):
    """
    Given a snappy manifold M, try to extract the associated link K
    Return K if successful, or None otherwise.
    Part of the point of the function is error trapping: snappy crashes
    if no link is found, but we do not want to crash.
    """
    K = None
    try:
        K = M.link()  # get the underlying knot or link
    except Exception as e:
        names = M.identify()
        for name in names:
            try:
                K = name.link()
                break
            except Exception as f:
                pass
    if K == None:
        verbose_print(verbose, 3, [M.name(), 'could not get link'])
    # Perhaps try to retriangulate, using tries
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


def name_and_link(in_obj, verbose=3):
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
        name = K.DT_code(DT_alpha=True)
        verbose_print(verbose, 10, [name, 'Received as link'])
    if type(in_obj) == str:
        name = in_obj
        verbose_print(verbose, 10, [name, 'Received as string'])
        if name[:2] == 'DT' or name[:2] == 'dt':  # We received a DT code
            K = snappy.Link(name)
        else:
            M = snappy.Manifold(name)
            K = link_from_manifold(M, verbose)
    return name, K


# Framing issues


def fix_framing(M):
    """
    Given a knot complement M, set the peripheral curves to be the homological
    meridian and longitude. This alters M and returns the change of basis matrix.
    """    
    meridian, _, _, _ = geom_tests.get_S3_slope_hyp(M)
    assert meridian is not None
    # If get_S3_slope fails, we should complain. Right now, it is in there as an assert.
    longitude = M.homological_longitude()
    sign = geom_tests.alg_int(meridian, longitude)
    assert sign == 1 or sign == -1
    meridian = (sign*a for a in meridian)
    cob = M.set_peripheral_curves([meridian, longitude])
    return cob
    

# Alexander polynomial and related invariants

# Casson_invt function used to be here; compare cosmetic_mfds.Casson_invt.
# The Casson invariant is now computed in Alexander_tests.

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
    Computes Casson invariant and genus lower bound together, so that Alexander
    polynomial is computed only once.
    """
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
    return int(A(1)/2), int(deg)


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
    Another bound we do not use is: g_T(K) <= c(K) - span V(K).
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



### 

# The following test is non-rigorous. It is designed to produce a flag that
# none of the rigorous tests have succeeded. We should not rely on it beyond that.
def is_exceptional_due_to_volume(M, verbose):
    # verbose = 100
    verbose_print(verbose, 6, [M.name(), "entering is_exceptional_due_to_volume"])
    if M.volume() < 0.9:
        verbose_print(verbose, 2, [M.name(), "has volume too small...(NON-RIGOROUS)"])
        verbose_print(verbose, 6, [M.fundamental_group()])
        return True
    

            
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
    verbose_print(verbose, 12, [M.name(), s, 'entering check_knot_cosmetic_slope'])

    name = M.name()
    sn = (s[0], -s[1])
    # if s and sn are parallel, skip
    if geom_tests.alg_int(s, sn) == 0:
        verbose_print(verbose, 12, [name, s, sn, 'are parallel'])
        return None

    s_hyp = geom_tests.is_hyperbolic_filling(M, s, m, l, tries, verbose)
    sn_hyp = geom_tests.is_hyperbolic_filling(M, sn, m, l, tries, verbose)

    if s_hyp == None:
        verbose_print(verbose, 6, [name, s, 'could not determine type'])
    if sn_hyp == None:
        verbose_print(verbose, 6, [name, sn, 'could not determine type'])
    if s_hyp == None or sn_hyp == None:
        verbose_print(verbose, 6, [name, s, sn, 'one of them is not recognized as hyp or except'])
        return (name, s, sn, 'one of them is not recognized as hyp or except')

    if (s_hyp and not sn_hyp) or (not s_hyp and sn_hyp):
        verbose_print(verbose, 6, [name, s, sn, 'only one is hyperbolic'])
        return None
    elif (s_hyp and sn_hyp):
        verbose_print(verbose, 6, [name, s, sn, 'both hyperbolic'])
        for i in range(tries):
            M = snappy.Manifold(M.triangulation_isosig())
            # Why do we replace M here??? 
            distinguished, rigorous = geom_tests.is_distinguished_by_hyp_invars(M, s, sn, i+1, verbose)
            if distinguished and rigorous:
                return None
            if distinguished and not rigorous:
                return (name, s, sn, 'seem to have different length spectra')
        return (name, s, sn, 'complex_vol_fail')
    else:
        assert( not s_hyp and not sn_hyp ) 
        if not( geom_tests.preferred_rep(s) == (1,1) or geom_tests.preferred_rep(s) == (1,-1) ):
            verbose_print(verbose, 6, [name, s, sn, 'exceptionals distinguished by Ravelomanana'])
            return None
        else:
            P = M.copy()
            Pn = M.copy()
            P.dehn_fill(s)
            Pn.dehn_fill(sn)
            out = geom_tests.torus_decomp_wrapper(P, tries, verbose)
            outn = geom_tests.torus_decomp_wrapper(Pn, tries, verbose)
            if out[0] != outn[0]:
                verbose_print(verbose, 2, [name, s, sn, 'exceptionals distinguished by Regina: only one is toroidal'])
                return None
            elif not out[0] or not outn[0]:
                # At least one of the fillings is atoroidal
                verbose_print(verbose, 2, [name, s, sn, 'exceptionals distinguished by Regina and Ravelomanana'])
                return None
            else:
                verbose_print(verbose, 0, [name, s, sn, out, outn, 'toroidal manifolds -- examine the pieces'])
                return (name, s, sn, 'toroidal manifolds '+str(out[1])+', '+str(outn[1]))




def systole_short_slopes(M, use_NiWu=True, tries=10, verbose=3):
    '''
    Given a knot complement M, presumed to be hyperbolic and equipped with
    the homological framing, compute the systole and use it to build a list of short
    slopes. 
    
    References: Thm 1.10 of EffectiveBilipschitz, plus strengthened theorem (currently 
    Thm 3.1) of the CosmeticByComputer paper.
    
    The flag 'use_NiWu' decides whether we prune the list of geometrically short
    slopes using the Ni-Wu constraint that p divides (q^2 + 1).
    Reference: [Ni-Wu, "Cosmetic surgeries on knots in S3"]
    '''
    
    name = M.name()

    for i in range(2*tries):
        try:
            sys = geom_tests.systole(M, verbose=verbose)
            # This is too slow.  Can we gain some time by using low precision for most manifolds?
            break
        except:
            sys = None
            verbose_print(verbose, 10, [name, 'systole failed on attempt', i])
            M.randomize()
    if sys == None:
        verbose_print(verbose, 6, [name, 'systole fail'])
        return None

    # get the translation lengths and the normalisation factor and bounds on p and q
    verbose_print(verbose, 2, [name, 'systole is at least', sys])
    # norm_len_cutoff = max(10.1, sqrt((2*pi/sys) + 58.0).n(200)) # Thm:CosmeticOneCusp
    norm_len_cutoff = max(9.97, sqrt((2*pi/sys) + 56.0).n(200)) 
    verbose_print(verbose, 4, [name, 'norm_len_cutoff', norm_len_cutoff])
    
	# Build list of short slopes in the homological framing. Note that the list we
	# receive from find_short_slopes is already in preferred_rep form.
    short_slopes_all = geom_tests.find_short_slopes(M, norm_len_cutoff, normalized=True, verbose=verbose)
    verbose_print(verbose, 4, [name, len(short_slopes_all), 'short slopes found'])
    verbose_print(verbose, 10, [short_slopes_all])

    # remove duplicate slopes, meridian, and longitude.
    # If use_NiWu==True, also remove all slopes that fail the Ni-Wu test.
    short_slopes = set()
    for s in short_slopes_all:
        p = s[0]
        q = s[1]
        if p == 0 or q ==0: 
            # No need to check (0,1) or (1,0) slopes - they cannot be cosmetic
            # by Gordon-Luecke and homology.
            continue
        if use_NiWu == True and (q**2 + 1) % p:  
            # Ni-Wu say p divides (q^2 + 1) in all cosmetics
            continue
        if geom_tests.preferred_rep((s[0], -s[1])) not in short_slopes:
            # That is, we have not yet added the negative of this slope
            verbose_print(verbose, 10, [name, s, 'adding to list of short slopes to check'])
            short_slopes.add(geom_tests.preferred_rep(s))
    verbose_print(verbose, 2, [name, len(short_slopes), 'short slopes left after pruning'])
    verbose_print(verbose, 4, [short_slopes])
    return short_slopes





def check_knot_cosmetic(knot, slope_method, use_NiWu = True, use_HFK = True, tries=10, verbose=3):
    '''
    Given a knot complement in S^3, install the homological framing on M
    and then check a list of slopes for being possibly a cosmetic pair.
    The list of slopes is determined by slope_method, which is one of:
    * 'Hanselman': check slope (2,1) and (1,q), where q obeys Hanselman's bound
    * 'FPS': check slopes that are shorter than a normalized length cutoff,
        determined by the systole as in FPS theorem
    * 'All': Do both of the above, and only check slopes in the overlap
    
    The flag 'use_HFK' decides how hard one works to form a list of Hanselman slopes.
    If true, we compute K.knot_floer_homology(); if not, we only use the
    Alexander polynomial and Turaev genus.
    The flag 'use_NiWu' decides whether we prune the list of geometrically short
    slopes using the Ni-Wu constraint that p divides (q^2 + 1).
    
    We do *not* pre-screen M using knot invariants. That pre-screening should
    happen in prune_using_invariants(...) instead.
    '''
    
    # Let's be liberal in what we accept
    name, M, K = name_manifold_and_link(knot, verbose=verbose)

    # But not too liberal
    assert geom_tests.is_knot_manifold(M)
    # Install the homological framing on M.
    cob = fix_framing(M)
    
    hom_slopes = None
    short_slopes = None
    
    if slope_method=='Hanselman' or slope_method=='All':
        hom_slopes = Hanselman_slopes(K, name, use_HFK, verbose)

    # From now on, we need geometry. So, check if the geometric
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
            return [(name, None, None, 'satellite knot: ' + str(out[1]))]
        # Anything else is confusing
        if is_exceptional_due_to_volume(M, verbose):   
            verbose_print(verbose, 2, [name, 'NON-RIGOROUS TEST says volume is too small']) 
            return [(name, None, None, 'small volume')]
        verbose_print(verbose, 2, [name, 'is very strange'])
        return [(name, None, None, 'very strange')]

    # Ok, at this point we are probably hyperbolic. Install a good hyperbolic metric.
    
    M = dunfield.find_positive_triangulation(M, tries=tries, verbose=verbose)
    
    m, l, norm_fac = geom_tests.cusp_invariants(M)
    verbose_print(verbose, 5, [name, 'cusp_stuff', 'merid', m, 'long', l, 'norm_fac', norm_fac])

    if slope_method=='FPS' or slope_method=='All':
        short_slopes = systole_short_slopes(M, use_NiWu, tries, verbose)
    
    if hom_slopes == None and short_slopes == None:
        verbose_print(verbose, 3, [name, 'could not get list of slopes using '+slope_method])
        return [(name, None, None, 'could not get list of slopes using '+slope_method)] 
    if hom_slopes == None and short_slopes != None:
        slopes = short_slopes
    if hom_slopes != None and short_slopes == None:
        slopes = hom_slopes
    if hom_slopes != None and short_slopes != None:
        # Take the intersection of the two lists
        slopes = set()
        for s in hom_slopes:
            if (s in short_slopes) or ((s[0], -s[1]) in short_slopes):
                slopes.add(s)
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


def collect_data_knots(knots, tries = 3, verbose = 3, report = 20):
    Casson_ruled_out = 0
    Jones_ruled_out = 0
    Torus_ruled_out = 0
    DNW_ruled_out = 0 # for Detcherry-Ni-Wu
    Satellites_found = 0
    Weird_geom_found = 0
    Short_systoles_found = 0
    shortest_systole = 1.0 # some sort of upper bound
    Long_list_found = 0
    longest_list = 0 # Longest list of slopes to check
    
    bad_uns = []
    for n, knot in enumerate(knots): 
        if n % report == 0:
            verbose_print(verbose, 0, ['report', n, bad_uns])
        knot_output = collect_data_knot_cosmetic(knot, tries, verbose)
        if knot_output == []:
            # Nothing at all interesting about this example
            continue
        if knot_output[0][1] == "Casson":
            Casson_ruled_out = Casson_ruled_out +1
            continue
        if knot_output[0][1] == "Jones_deriv":
            Jones_ruled_out = Jones_ruled_out +1
            continue
        if knot_output[0][1] == "torus":
            Torus_ruled_out = Torus_ruled_out +1
            continue
        if knot_output[0][1] == "satellite":
            Satellites_found = Satellites_found +1
            bad_uns.extend(knot_output)
            continue
            

        # From here on, we should be doing hyperbolic stuff
        if knot_output[0][1] == "weird":
            Weird_geom_found = Weird_geom_found +1
            bad_uns.extend(knot_output)
            continue
            
        if knot_output[0][1] == "systole":
            if knot_output[0][2] == None:
                Weird_geom_found = Weird_geom_found +1
                bad_uns.extend(knot_output)
                continue
            else:
                Short_systoles_found = Short_systoles_found +1
                bad_uns.extend(knot_output[0])
                sys = knot_output[0][2]
                if sys < shortest_systole:
                    shortest_systole = sys
            del knot_output[0]
        if knot_output == []:
            continue

        emptylist = False
        for i in range(len(knot_output)):
            if knot_output[i][1] == "emptylist":
                DNW_ruled_out = DNW_ruled_out + 1
                emptylist = True
                break
        if emptylist:
            continue

        for i in range(len(knot_output)):
            if knot_output[i][1] == "biglist":
                Long_list_found = Long_list_found +1
                list_length = knot_output[i][2]
                if list_length > longest_list:
                    longest_list = list_length
                break

        bad_uns.extend(knot_output)
        
    if verbose > 0:
        print('final report', n+1, ':')
        print(Casson_ruled_out, 'ruled out by Casson')
        print(Jones_ruled_out, 'ruled out by Jones')
        print(Torus_ruled_out, 'ruled out as torus knots')
        print(Satellites_found, 'satellite knots found')
        print(Weird_geom_found, 'knots with undetermined geometry')
        print(Short_systoles_found, 'hyperbolic knots with systole < 0.15')
        print(shortest_systole, 'shortest systole')
        print(DNW_ruled_out, 'knots with no slopes to check after Detcherry and Ni-Wu tests')
        print(Long_list_found, 'knots with >2 pairs of slopes to check by geometry')
        print(longest_list, 'maximum pairs of slopes to check')
        print(bad_uns)
    return bad_uns



def prune_using_invariants(knots, Casson=True, Hanselman_quick=True, Jones_deriv=True, Jones_fifth=True, Tau_test=True, Wang=True, Hanselman_HFK=True, verbose=3, report=100):
    '''
    Given a list of knots or knot complements, tries to
    rule out cosmetic surgeries using the followifng tests:
    * Boyer-Lines test (second derivative of Alexander polynomial at 1) 
    * quick Hanselman test (span(Alexander) and Turaev genus)
    * Ichihara-Wu test (third derivative of Jones polynomial at 1)
    * Detcherry test (Jones polynomial at 5th root of 1) 
    * Ni-Wu test (tau invariant)
    * Wang test (genus one knots)
    * HFK Hanselman test (exact genus and HFK thickness)

    The tests are ordered according to speed, for a typical non-alternating knot. 
    Note that if K is alternating, then computing HFK is super-fast because Szabo's
    program is written in C and the invariant is little more than the Alexander
    polynomial. Thus, for alternating knots, it is advisable to turn off the
    non-HFK tests for speed.
    
    Returns a list of only those knots for which  these tests do not succeed. 
    The remaining knots would have to be checked using hyperbolic methods.
    '''

    bad_uns = []
    Casson_ruled_out = 0
    Hansel_quick_ruled_out = 0
    Jones_ruled_out = 0
    Detcherry_ruled_out = 0
    Tau_ruled_out = 0
    Wang_ruled_out = 0
    Hansel_full_ruled_out = 0

    for n, knot in enumerate(knots):
        if verbose > 0 and n % report == 0:
            print('report', n, ':', Casson_ruled_out, 'ruled out by Casson invariant,', Hansel_quick_ruled_out, 'ruled out by quick genus-thickness test,', Jones_ruled_out, 'ruled out by Jones derivative,')
            print(Detcherry_ruled_out, 'ruled out by Jones 5th root of 1,', Tau_ruled_out, 'ruled out by tau invariant,', Wang_ruled_out, 'ruled out b/c genus=1,', Hansel_full_ruled_out, 'ruled out by HFK thickness and genus')
            print('Last few difficult knots', bad_uns[-5:])

        # Be somewhat generous in what we accept
        name, K = name_and_link(knot, verbose=verbose)
        # We use K to compute all of the invariants.
        # The Alexander polynomial can be computed from the fundamental group (hence from M),
        # but this is much slower.

        # Collect Alexander polynomial data
        if Casson or Hanselman_quick: # if we need the Alexander polynomial
            C, genus_bound = Alexander_tests(K, name, verbose=verbose)

        # Boyer-Lines test via Casson invt, second derivative of the Alexander polynomial
        if Casson:
            if C != 0:
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Boyer-Lines'])
                Casson_ruled_out = Casson_ruled_out + 1
                continue

        # Get a cheap upper bound on HFK thickness from Turaev genus
        if Hanselman_quick or Jones_fifth:
            th = thickness_upper_bound(K, name, verbose)
            if th == None:
                th = 1000 # some outrageously large value
        
        # Apply the quick Hanselman test. The inequality below, namely
        # 'th < 2*g*(g-2)', becomes harder to satisfy when th goes up and
        # g goes down.
        # Consequently, it is safe to substitute a cheap lower bound on genus
        # (namely, span(Alexander)/2) and a cheap upper bound on thickness
        # (namely, the Turaev genus of the diagram).
        if Hanselman_quick:
            g = genus_bound
            verbose_print(verbose, 6, [name, 'quick Hanselman test', th, 2*g*(g-2)])
            if th < 2*g*(g-2):
                # The above inequality is never true when g=0,1,2, because th >= 0.
                # For g >= 2, it is equivalent to (th + 2*g)/(2*g*(g-1)) < 1, which is the
                # criterion in Hanselman's Theorem 2.
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by quick Hanselman test'])
                Hansel_quick_ruled_out = Hansel_quick_ruled_out + 1
                continue
            # The following sub-test perhaps deserves its own 'quick Wang' flag
            if th == 0 and g == 1: 
                # These must be alternating knots of genus exactly 1
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Wang for alternating knots'])
                Hansel_quick_ruled_out = Hansel_quick_ruled_out + 1
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
            D = jones_data[1]  # V_K(zeta5)
            verbose_print(verbose, 6, [name, 'th(K) <=', th, ', V_K(zeta5) =', D])
            if (th != None and th < 16) and (D != None and D != 1):
                # See the proof of Corollary 1.5 in Detcherry's paper.
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Detcherry'])
                Detcherry_ruled_out = Detcherry_ruled_out + 1
                continue

        # Compute knot floer homology plus related numbers, if needed
        if Tau_test or Wang or Hanselman_HFK:
            tau, g, th = HFK_tests(K, name, verbose)
        
        # Ni-Wu test, tau invariant
        if Tau_test:
            if tau != None and tau != 0:
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Ni-Wu'])
                Tau_ruled_out = Tau_ruled_out + 1
                continue
            
        # Wang test, genus one knots
        if Wang:
            if g == 1:
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Wang'])
                Wang_ruled_out = Wang_ruled_out + 1
                continue

        # Hanselman HFK test: use the real genus and thickness
        if Hanselman_HFK and th != None and g != None:
            verbose_print(verbose, 6, [name, 'Full Hanselman test', th, 2*g*(g-2)])
            if th < 2*g*(g-2):
                # The above inequality is never true when g=0,1,2, because th >= 0.
                # For g >= 2, it is equivalent to (th + 2*g)/(2*g*(g-1)) < 1, which is the
                # criterion in Hanselman's Theorem 2.
                verbose_print(verbose, 3, [name, 'has no cosmetic surgeries by Hanselman genus-thickness test'])
                Hansel_full_ruled_out = Hansel_full_ruled_out + 1
                continue

        # At this point, all the above tests have failed.
        bad_uns.append(name)
        
    if verbose > 0:
            print('report', n+1, ':', Casson_ruled_out, 'ruled out by Casson invariant,', Hansel_quick_ruled_out, 'ruled out by quick genus-thickness test,', Jones_ruled_out, 'ruled out by Jones derivative,')
            print(Detcherry_ruled_out, 'ruled out by Jones 5th root of 1,', Tau_ruled_out, 'ruled out by tau invariant,', Wang_ruled_out, 'ruled out b/c genus=1,', Hansel_full_ruled_out, 'ruled out by HFK thickness and genus')
    return bad_uns



def check_knots(knots, slope_method = 'All', use_NiWu = True, use_HFK = True, tries=10, verbose=4, report=20):
    
    bad_uns = []
    for n, knot in enumerate(knots): 
        out = check_knot_cosmetic(knot, slope_method, use_NiWu, use_HFK, tries, verbose)
        bad_uns.extend(out)
        if n % report == 0: 
            verbose_print(verbose, 0, ['report', n, bad_uns])
    return bad_uns

