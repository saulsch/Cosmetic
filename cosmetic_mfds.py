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


def are_distinguished_lens_spaces(name0, name1, verbose = 3):
    # Only tests for _un_oriented homeomorphism... urk!
    bool0, ints0 = is_lens_space_from_name(name0)
    bool1, ints1 = is_lens_space_from_name(name1)
    if not (bool0 and bool1):
        verbose_print(verbose, 12, [name0, name1, "at least one is not a lens space"])
        return False
    p0, q0 = ints0
    p1, q1 = ints1
    if p0 != p1:
        verbose_print(verbose, 0, [name0, name1, "lens spaces with different homology"])
        # threshold is low because we expect this to never happen.  [grin]
        return True
    p = p0
    if ((q0 - q1) % p) == 0 or ((q0 + q1) % p) == 0 or ((q0 * q1) % p) == 1 or ((q0 * q1) % p) == -1 % p:
        verbose_print(verbose, 12, [name0, name1, "homeomorphic lens spaces"])
        return False
    verbose_print(verbose, 12, [name0, name1, "non-homeomorphic lens spaces"])
    return True


def is_sfs_over_s2_from_name(name):
    """
    Given a regina name, if it is a SFS over S^2 (and not a lens
    space) return True and the coefficients.
    """
    # Note that we don't count lens spaces as SFSs.  [grin]
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


def are_distinguished_sfs_over_s2(name_0, name_1, verbose = 3):
    # Only tests for _un_oriented homeomorphism... urk
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

    eul_num_0 = sum( QQ((q, p)) for (p, q) in coeffs_0 )
    eul_num_1 = sum( QQ((q, p)) for (p, q) in coeffs_1 )
    
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


def has_orientation_reversing_symmetry_from_name(name, verbose = 3):
    # https://math.stackexchange.com/questions/2843946/which-lens-spaces-are-chiral
    # "Example 3.22 and Lemma 3.23 in Hempel give q^2 + 1 = 0 (mod p)
    # as a necessary and sufficient condition for L(p,q) to admit an
    # orientation-reversing homeomorphism."
    is_lens, ints = is_lens_space_from_name(name)
    if is_lens:
        p, q = ints
        return ((q**2 + 1) % p) == 0
    # homework - add sfs's and JSJ's here as well. 
    

# Math

    
def product(nums):
    prod = 1
    for d in nums:
        prod = prod * d
    return prod


# Volume drops


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
    return (3.3957/4.0) * ( (-2*z**5 + z**4 - z**3 + 2*z**2 - z + 1)/(z**2 + 1)**2 + arctan(z) - arctan(RIF(1)) )

# Recall that HK_vol_bound is decreasing (for L > 5.6 or so).  So we may
# use bisection to invert.
# Is this really fast enough?  I guess so...

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
# criterion on Alexander polynomial

def A_invt(M, verbose):
    P = M.alexander_polynomial()
    if verbose > 10:
        print(P, 'Alexander polynomial')
    deg = P.degree()/2
    Rin = P.parent()  # the polynomial ring where P lives
    # Assume that P is a polynomial in one variable
    # normalize the polynomial so that positive and negative powers match and
    # so that it evaluates to 1 at 1
    Q = P/(Rin.gen()**deg * P(1))  
    if verbose > 10:
        print(Q, 'Normalized Alexander polynomial')
    assert Q(1) == 1
    A = Q.derivative().derivative()
    if verbose > 10:
        print(A, 'second derivative')
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


def check_cover_homology_fixed_deg(M, N, deg, verbose=10):
    """
    Given a pair of snappy manifolds, M and N, and a degree deg,
    build all covers of M and N of degree deg. Compute homology groups of each.
    Check whether the sets match.
    """

    M_homologies = set( str(K.homology()) for K in M.covers(deg))
    N_homologies = set( str(K.homology()) for K in N.covers(deg))

    if verbose > 12:
        print(M, 'degree', deg, M_homologies)
        print(N, 'degree', deg, N_homologies)

    if M_homologies != N_homologies:
        if verbose > 2:
            print(M, N, 'distinguished by cover homology at degree', deg)
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
        if verbose > 6:
            print(M, s, t, "cover spectrum distinguishes")
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
        if verbose > 5:
            print(Ms, Ms.homology(), ',', Mt, Mt.homology(), 'distinguished by homology groups')
        return True

    order = order_of_torsion(Ms)
    if order == 1:
        # urk
        if verbose > 5:
            print(Ms, Mt, "are Z homology three-spheres. Cool!")
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


def is_amphichiral(M):
    """
    Given an orientable hyperbolic cusped Snappy three-manifold,
    decides if it has an orientation reversing isometry.
    """
    assert M.solution_type() == 'all tetrahedra positively oriented'
    assert M.is_orientable()
    assert M.num_cusps() > 0

    G = M.symmetry_group()
    return G.is_amphicheiral()


### This function is not rigorous - also it is never called.  So we
### should delete this...
def is_exceptional_due_to_volume(M, verbose):
    if verbose > 12: print(M, 'entering is_exceptional_due_to_volume')
    if M.volume() < 0.9:
        if verbose > 6: print(M, 'has volume too small...')
        if verbose > 6: print(M.fundamental_group())
        return True


def fetch_exceptional_data(M, s, exceptions_table, field, tries = 3, verbose = 2):
    '''
    Given a manifold M (assumed to be one-cusped) we wish to construct
    and update the exceptions_table.  This is a database where the
    keys are slopes (here s).  The fields are useful data about
    exceptional fillings that we don't want to compute twice.  Remark:
    If we fail to compute an invariant, we don't install anything in
    the table and just return None.
    '''
    # convention - no empty fields - aka no placeholders. 

    if verbose > 12:
        print(M, s, "entering exceptions table", field)
    
    allowed_fields = ["fund_gp", "name", "lens", "sfs_over_s2", "reducible", "toroidal"]
    assert field in allowed_fields
    
    if not s in exceptions_table:
        exceptions_table[s] = {}

    if field in exceptions_table[s]:
        if verbose > 10:
            print(M, s, field, 'found in table')
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
            if verbose > 10:
                print(N, name, 'added to table')
            return name
        else:
            if verbose > -1:
                print(N, "could not compute name")
            return None

    if field == "lens":
        name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
        if name == None:
            return (None, None)

        out = is_lens_space_from_name(name)
        is_lens, _ = out
        if is_lens: 
            exceptions_table[s]["lens"] = out
            if verbose > 10:
                print(N, name, 'lens coeffs added to table')
            return out
        else:
            if verbose > 10:
                print(N, name, 'no lens coeffs found')
            return out
    
    if field == "sfs_over_s2":
        name = fetch_exceptional_data(M, s, exceptions_table, "name", tries, verbose)
        if name == None:
            return (None, None)

        out = is_sfs_over_s2_from_name(name)
        is_sfs_over_s2, _ = out
        if is_sfs_over_s2: 
            exceptions_table[s]["sfs_over_s2"] = out
            if verbose > 10:
                print(N, name, 'sfs coeffs added to table')
            return out
        else:
            if verbose > 10:
                print(N, s, name, 'no sfs coeffs found')
            return out
        
    if field == "reducible":
        out = geom_tests.is_reducible_wrapper(N, tries, verbose)
        exceptions_table[s]["reducible"] = out
        if verbose > 10:
            print(N, out, 'reducibility')
        return out
        
    if field == "toroidal":
        out = geom_tests.is_toroidal_wrapper(N, tries, verbose)
        exceptions_table[s]["toroidal"] = out
        if verbose > 10:
            print(N, out, 'toroidality')
        return out
        

def fetch_volume(M, s, volumes_table, tries, verbose):
    '''
    Given a manifold M (assumed to be one-cusped and equipped with a
    good triangulation) and a slope s (assumed to be hyperbolic),
    fetch the volume. This means: pull the volume from the table
    if it is there; else, try to compute it, and then store in the table.
    Return the volume either way.
    '''
    if verbose > 12:
        print(M, s, "entering fetch_volume")

    if s in volumes_table:
        if verbose > 10:
            print(M, s, 'volume found in table')
        return volumes_table[s]
    else:
        if verbose > 10:
            print(M, s, 'trying to compute volume')
                
        assert M.solution_type() == 'all tetrahedra positively oriented'

        N = M.copy() 
        N.dehn_fill(s)

        # will need to wrap this in a try/except. 
        is_hyp, vol = dunfield.is_hyperbolic_with_volume(N, tries = tries, verbose = verbose)
        if not is_hyp:
            if verbose > -1:
                print(N, 'positive triangulation fail - putting untrusted volume in the table')
            R = RealIntervalField(10) # downgrade the precision!
            volumes_table[s] = R(N.volume())
        else: 
            volumes_table[s] = vol

    return volumes_table[s]
        
        # if verbose > 10:
        #     print(N, 'computing verified volume')
        # for i in range(tries):
        #     # for next time - we should be willing to take covers someplace here.  
        #     try:    
        #         volumes_table[s] = P.volume(verified = True, bits_prec=prec)
        #         return volumes_table[s]
        #     except RuntimeError: # hackedy-hack
        #         if verbose > 5:
        #             print(N, 'Volume computation failed at precision', prec)
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
    if verbose > 12: print(M, s, 'entering is_hyperbolic_filling')
    p, q = s
    # We don't recompute cusp_invariants because it is slow
    # m, l, _ = cusp_invariants(C)
    if abs(p*mer_hol + q*long_hol) > 6: # six-theorem
        if verbose > 12: print(M, s, 'has length', abs(p*mer_hol + q*long_hol), 'hence the filling is hyperbolic by 6-theorem')
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
    if verbose > -1:
        print(name, "think about adding this to the rules above!")
    return None


# geometry -

def systole(M, verbose = 2):
    if verbose > 12:
        print(M, "entering systole")
    spec = M.length_spectrum(0.15, full_rigor = True) # Ok - what does 'full-rigor' actually mean?
    if verbose > 12:
        print(M, "computed length spectrum")
    if spec == []:
        return 0.15 # any systole larger than this gets ignored. 
    else:
        return spec[0].length.real()

    
# dealing with a pair of slopes

def is_distinguished_by_hyp_invars(L, s, t, tries, verbose):
    '''
    Given a manifold L and two slopes (where we think that both
    fillings are hyperbolic), try to prove that L(s) is not
    orientation-preservingly homeomorphic to L(t).
    '''
    if verbose > 12: print(L, s, t, 'entering is_distinguished_by_hyp_invars')
    M = L.copy()
    M = dunfield.find_positive_triangulation(M, tries) # We could ask for more - a positive triangulation with good shapes!

    if M == None:
        if verbose > 6: print(L, 'positive triangulation fail')
        return None
    
    M.chern_simons() # must initialise - see docs
    N = M.copy()

    M.dehn_fill(s)
    N.dehn_fill(t)
    M = dunfield.find_positive_triangulation(M, tries) 
    N = dunfield.find_positive_triangulation(N, tries)

    if M == None or N == None:
        if verbose > 6: print(L, s, t, 'positive triangulation fail')
        return None

    prec = 40 # note the magic number 40.  Fix.
    for i in range(tries):
        try:
            # Chern-Simons is not trustworthy...
            if abs(M.chern_simons() - N.chern_simons()) > 1.0/1000:
                if verbose > 6:
                    print(L, s, t, 'chern simons distinguishes')
                return True

            prec = prec * 2
	    # Volume is more trustworthy but of course slower
            if abs(M.volume(verified = True, bits_prec=prec) - N.volume(verified = True, bits_prec=prec)) > 4* (1/2)**prec:
                # Hmm.  If we've just computed to high precision, we should update the table?
                if verbose > 6:
                    print(L, s, t, 'volume distinguishes at precision', prec)
                return True

            # "full rigor" isn't. 
            M_spec = M.length_spectrum(full_rigor=True)
            N_spec = N.length_spectrum(full_rigor=True)

            if len(M_spec) > 0 and len(N_spec) > 0:
                # let's be careful to avoid handedness issues
                m = M_spec[0].length.real()
                n = M_spec[0].length.real()
                if abs(m - n) > 0.1: 
                    if verbose > 0:
                        print(L, s, t, "bottom of length spectrum distinguishes")
                    return True

            M_multi = [a.multiplicity for a in M.length_spectrum(2, full_rigor=True)]
            N_multi = [a.multiplicity for a in N.length_spectrum(2, full_rigor=True)]

            if M_multi != N_multi:
                if verbose > 0:
                    print(L, s, t, "bottom of multiplicity spectrum distinguishes")
                return True
            
        except Exception as e:
            if verbose > 6: print(L, s, t, e)
            M.randomize()
            N.randomize()
    
    return None        


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
    if verbose > 12: print(L, s, t, 'entering is_distinguished_non_hyp')
    M = L.copy()
    N = L.copy()
    
    M.dehn_fill(s)
    N.dehn_fill(t)

    # finish or delete
    
    return None        


def check_hyperbolic_slope_pair(M, s, t, tries, verbose):
    '''               
    Given a one-cusped manifold M and a pair of slopes s and t, which
    are presumed to be hyperbolic, decides if they are possibly a
    cosmetic pair.  If they are not, returns None -- if they are
    (possibly) return the reason why they might be.
    '''

    if verbose > 24: print(M, s, 'entering check_hyperbolic_slope_pair')
    name = M.name()

    for i in range(tries):
        M = snappy.Manifold(name)
        if is_distinguished_by_hyp_invars(M, s, t, i+1, verbose):
            return None
    return (name, s, t, 'Not distinguished by hyperbolic invariants')


def check_cosmetic(M, tries, verbose):
    '''
    Given a one-cusped manifold M we equip it with a shortest framing
    and then return a list of tuples - (name, s, t, 'reason') where s
    and t are possibly a cosmetic pair.
    '''

    if verbose > 12:
        print("entering check_cosmetic")
    
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

    h = M.homology()
    if h.betti_number() == 1 and h.rank() == 1:
        # M is the complement of a knot in an integer homology sphere
        if A_invt(M, verbose) != 0:
            # The second derivative of the Alexander polynomial at 1 is nonzero,
            # so M has no cosmetic surgeries by Boyer-Lines
            if verbose > 2: print(M, 'has no cosmetic surgeries by Boyer-Lines')
            return []

    # Before we try to think _too_ deeply, we check if the geometric
    # structure is good enough.

    if not dunfield.verify_hyperbolic_basic(M, verbose = verbose):
        # M is probably not a hyperbolic manifold.  Let's do a few
        # quick tests to help ourselves later, and then give up.
        if is_torus_link_filling(M, verbose):
            # M is a torus knot, so it has non-zero tau invariant, and
            # so by Ni-Wu satisfies the cosmetic surgery conjecture
            if verbose > 6: print(M, 'is a torus knot; no cosmetic surgeries by Ni-Wu')
            return []
        out = fundamental.is_toroidal_wrapper(M, tries, verbose)
        if out[0]: 
            # M is toroidal, so use the torus decomposition as the 'reason'
            if verbose > 6: print(M, 'is toroidal')
            return [(name, None, None, 'toroidal mfd: ' + str(out[1]))]
        # 'How did I get here?' -- Talking Heads.
        if is_exceptional_due_to_volume(M, verbose):
            if verbose > -1: print(M, 'non-rigorous volume is too small...')
            return [(name, None, None, 'small volume')]
        if verbose > 2:
            print(M, 'bad solution type for unclear reasons...')
        return [(name, None, None, 'bad solution type - strange!')]
                
    # Ok, at this point we are probably hyperbolic.

    # Step zero - Initialize. find the systole. 

    volumes_table = {}  # Lookup table of volumes of hyperbolic fillings
    exceptions_table = {}  # Lookup table of information about non-hyperbolic fillings
        
    for i in range(2*tries): # that looks like a magic number... 
        try:
            M = snappy.Manifold(name)
            if i % 2 == 1: 
                M = M.high_precision()
            for j in range(i):
                M.randomize()
            sys = systole(M, verbose = verbose)
            break
        except:
            sys = None
            if verbose > 10:
                print(M, 'systole failed on attempt', i)
        
    if sys == None:
        if verbose > 6: print(name, None, None, 'systole fail')
        return [(name, None, None, 'systole fail')]

    if verbose > 2: print(name, 'systole is at least', sys)
    # norm_len_cutoff = max(10.1, sqrt((2*pi/sys) + 58.0).n(200))
    norm_len_cutoff = max(9.97, sqrt((2*pi/sys) + 56.0).n(200)) 
    if verbose > 4: print(name, 'norm_len_cutoff', norm_len_cutoff)
    
    # Step one - fix the framing and gather the invariants that can
    # be found rigorously.

    # Switch to low precision to save time now. 
    M = snappy.Manifold(name)
    M.set_peripheral_curves('shortest')
    # C = M.cusp_neighborhood()
    # C.set_displacement(C.stopping_displacement())
    mer_hol, long_hol, norm_fac = geom_tests.cusp_invariants(M)
    l_hom = geom_tests.preferred_rep(M.homological_longitude())
    m_hom = geom_tests.shortest_complement(l_hom, mer_hol, long_hol)
    
    if verbose > 4: print(name, 'cusp_stuff', 'merid', mer_hol, 'long', long_hol)
    if verbose > 4: print(name, 'cusp_stuff', 'norm_fac', norm_fac, 'homolog. long.', l_hom, 'homolog. merid.', m_hom)
    
    # Step two - gather the invariants of M that cannot currently be
    # found rigorously.
    
    # To be correctly careful we need to either increase the
    # len_cutoff, or we need to trap it in an interval.  Anyway. 
    
    len_cutoff = norm_len_cutoff * norm_fac
    if verbose > 2: print(name, 'len_cutoff', len_cutoff)
    a_max = int(ceil(len_cutoff/abs(mer_hol)).endpoints()[0])
    b_max = int(ceil(len_cutoff/abs(long_hol)).endpoints()[0])
    if verbose > 4: print(name, 'maximal mer coeff', a_max, 'merid length', abs(mer_hol).endpoints()[0])
    if verbose > 4: print(name, 'maximal long coeff', b_max, 'long length', abs(long_hol).endpoints()[0])

    # Step three - get the short slopes
    
    short_slopes = []
    for a in range(0, a_max + 1): # do not need neg a as (a,b) = (-a,-b) is preserved by framing change
        for b in range(-b_max, b_max + 1):
            if gcd(a, b) == 1 and abs(a*mer_hol + b*long_hol) <= len_cutoff:    
                short_slopes.append(geom_tests.preferred_rep((a, b)))
                
    if verbose > 2: print(name, len(short_slopes), 'short slopes found')
    if verbose > 3: print(short_slopes)

    slopes_by_homology = {}
    for s in short_slopes:
        p = abs(geom_tests.alg_int(s, l_hom))
        if p == 0:
            continue # the homological longitude is unique, so cannot be cosmetic
        N = M.copy()
        N.dehn_fill(s)
        hom_gp = str(N.homology())
        
        # This test fails and also is unnecessary.  See Lem:TorsionInHalfLivesHalfDies
        # assert ( ( order_of_torsion(N) / order_of_torsion(M) ) - p ) < 0.01, str(M.name()) + ' ' + str(s)
        
        hom_hash = (p, hom_gp)  # Note that p is redunant by Lemma~\ref{Lem:HomologyTorsion}
        add_to_dict_of_sets(slopes_by_homology, hom_hash, s)

    if verbose > 3: print(name, 'slopes_by_homology', slopes_by_homology)
        
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

    if verbose > 3: print(name, 'hyp slopes', slopes_hyp)
    if verbose > 3: print(name, 'non-hyp slopes', slopes_non_hyp)
    if verbose > 3: print(name, 'bad slopes', slopes_bad)

    # Step five - Compute the max of the volumes in
    # slopes_hyp[hom_hash] and use this to compute the larger set of
    # "comparison slopes".

    max_volumes = {}
    for hom_hash in slopes_hyp:
        max_vol = 0
        for s in slopes_hyp[hom_hash]:
            vol = fetch_volume(M, s, volumes_table, tries, verbose)            
            if vol > max_vol: max_vol = vol
        max_volumes[hom_hash] = max_vol

    if verbose > 3: print(name, 'max volumes by homology', max_volumes)

    # len_m_hom = abs(m_hom[0]*mer_hol + m_hom[1]*long_hol)
    len_l_hom = abs(l_hom[0]*mer_hol + l_hom[1]*long_hol)
    slopes_low_volume = {}
    for hom_hash in slopes_hyp:
        if verbose > 25:
            print('slopes hyp', slopes_hyp[hom_hash])
        M_vol = fetch_volume(M, (0,0), volumes_table, tries, verbose)
        if verbose > 25:
            print('M_vol', M_vol)
        l_max = HK_vol_bound_inv(M_vol - max_volumes[hom_hash]) * norm_fac # length on cusp
        if verbose > 25:
            print('hom_hash, max_vol[hom_hash]', hom_hash, max_volumes[hom_hash])
            print('l_max', l_max, HK_vol_bound_inv(M_vol - max_volumes[hom_hash]))
            print('div ends', (l_max/norm_fac).endpoints(),)
            print('norm_fac', norm_fac.endpoints())
            print('len_l_hom', len_l_hom)

        p, hom_gp = hom_hash
        point = (p*m_hom[0], p*m_hom[1])
        middle = geom_tests.a_shortest_lattice_point_on_line(point, l_hom, mer_hol, long_hol)
        lower = int( (-l_max / len_l_hom).floor().lower() )
        upper = int( (l_max / len_l_hom).ceil().upper() )
        if verbose > 25: print('lower, upper', lower, upper)
        for k in range(lower, upper + 1):
            if verbose > 25: print('k', k)
            # move along the line 
            a = middle[0] + k * l_hom[0] 
            b = middle[1] + k * l_hom[1]
            t = geom_tests.preferred_rep((a, b))
            a, b = t
            if verbose > 25: print('t', t)
            if gcd(a, b) > 1:
                if verbose > 25: print(name, hom_hash, k, t, 'excluded because gcd')
                continue
            N = M.copy()
            N.dehn_fill(t)
            hom_gp_t = str(N.homology())
            if hom_gp_t != hom_gp:
                if verbose > 25: print(name, hom_hash, k, t, 'excluded because wrong homology')
                continue
            # now we now that (p, hom_gp_t) are correct, so we can use the dictionaries we built
            if hom_hash in slopes_non_hyp and t in slopes_non_hyp[hom_hash]:
                if verbose > 25: print(name, hom_hash, k, t, 'excluded because non-hyp')
                continue
            if hom_hash in slopes_bad and t in slopes_bad[hom_hash]:
                if verbose > 25: print(name, hom_hash, k, t, 'excluded because bad')
                continue
            # Thus t is a hyperbolic filling, so 
            # First, check length
            if verbose > 25: print('lengths', abs(a*mer_hol + b*long_hol), l_max)
            if abs(a*mer_hol + b*long_hol) <= l_max:
                # Then, check the volume
                t_vol = fetch_volume(M, t, volumes_table, tries, verbose)
                if verbose > 25: print('t_vol', t_vol)
                if verbose > 25: print('max_vol[hom_hash]', max_volumes[hom_hash])
                if not t_vol > max_volumes[hom_hash]:   # We need the 'not' because we are comparing intervals
                    add_to_dict_of_sets(slopes_low_volume, hom_hash, t)
                    if verbose > 25: print('added one???')
        # Sanity check: slopes_hyp[hom_hash] should be a subset of slopes_low_volume[hom_hash]
        for t in slopes_hyp[hom_hash]:
            a, b = t
            if not t in slopes_low_volume[hom_hash]:
                print(name, hom_hash, t, 'hyp slope did not make it into slopes_low_volume')

    if verbose > 3: print(name, '(somewhat-)low volume slopes', slopes_low_volume)

    # Step six - check for cosmetic pairs in slopes_non_hyp[hom_hash].
    # Note that slopes_bad automatically gets recorded and reported.

    bad_uns = []
    for hom_hash in slopes_bad:
        for s in slopes_bad[hom_hash]:
            reason = (name, hom_hash, s, 'Could not verify hyperbolicity')
            if verbose > 2:
                print(reason)
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
                        if verbose > 2: print(reason)
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
                        if verbose > 2: print(reason)
                        bad_uns.append(reason)
                        continue

                if s_lens or s_sfs:
                    t_red, _ = fetch_exceptional_data(M, t, exceptions_table, "reducible", tries, verbose)
                    if t_red:
                        continue
                    
                if t_lens or t_sfs:
                    s_red, _ = fetch_exceptional_data(M, s, exceptions_table, "reducible", tries, verbose)
                    if s_red:
                        continue                    
                
                if s_lens or s_sfs:
                    t_tor, _ = fetch_exceptional_data(M, t, exceptions_table, "toroidal", tries, verbose)
                    if t_tor:
                        continue

                if t_lens or t_sfs:
                    s_tor, _ = fetch_exceptional_data(M, s, exceptions_table, "toroidal", tries, verbose)
                    if s_tor:
                        continue

                # more tests here
                    
                if is_distinguished_by_cover_homology(M, s, t, tries, verbose):
                    continue

                # or here

                if verbose > 2: print(reason)
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
                if verbose > 12:
                    print(M, s, t, s_vol, t_vol, 'volumes')
                if s_vol > t_vol or t_vol > s_vol:
                    if verbose > 6: print(M, s, t, 'verified volume distinguishes')
                    continue
                if is_distinguished_by_hyp_invars(M, s, t, tries, verbose):
                    continue
                reason = (name, s, t, 'Not distinguished by hyperbolic invariants')
                if verbose > 2: print(reason)
                bad_uns.append(reason)

    if verbose > 3: print(name, 'non-distinguished pairs', bad_uns)
    if verbose > 3: print(name, 'non-hyp slopes', slopes_non_hyp)
    if verbose > 3: print(name, 'bad slopes', slopes_bad)

    # Step seven - deal with (unordered, distinct) pairs from slopes_non_hyp

    return bad_uns
    
def check_mfds(manifolds, tries, verbose, report = 10):
    if verbose > 12:
        print("entering check_mfds")
    amphichiral_uns = []
    bad_uns = []
    for n, M in enumerate(manifolds):
        if type(M) is snappy.Manifold:
            name = M.name()
        if type(M) == str:
            name = M
            M = snappy.Manifold(name)
        uns = check_cosmetic(M, tries, verbose)
        if is_amphichiral(M):
            if len(uns) > 0:
                if verbose > -1: 
                    for line in uns:
                        print(" is amph", line    )
                amphichiral_uns.extend(uns)
        else:
            if len(uns) > 0:
                if verbose > -1: 
                    for line in uns:
                        print("not amph", line    )
                bad_uns.extend(uns)
        if n > 0 and n % report == 0:
            print(n)
    return amphichiral_uns, bad_uns

