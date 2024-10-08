#
# fundamental.py
#

# Goal - Recognize and distinguish manifolds using their fundamental group and covers.

import snappy
from sage.interfaces.gap import gap
from verbose import verbose_print
from dunfield import closed_isosigs


# arithmetic


def product(nums):
    prod = 1
    for d in nums:
        prod = prod * d
    return prod


# combinatorics of words


def get_first_syl(w):
    """
    Given a word w, return the first syllable and the remaining suffix.
    """
    assert len(w) > 0
    a = w[0]
    n = 0
    while n < len(w) and w[n] == a:
        n = n + 1
    return (w[:n], w[n:])


def get_syls(w):
    """
    Given a word w, break it into syllables.
    """
    syls = []
    while len(w) > 0:
        syl, w = get_first_syl(w)
        syls.append(syl)
    return syls


# Standing assumptions: relations have non-zero length.  Also,
# generators are letters.  (If there are more than 26 generators then
# something is probably very wrong...)

# Strings are not a commutative monoid, so the notation python uses is
# "wrong"; it uses a + b for concatenation, instead of a*b, and uses
# a*n for powers, instead of a^n.  Silly computer scientists!


# working with relations


def is_cyclic_relation(rel):
    # if rel == a^n
    syls = get_syls(rel)
    return len(syls) == 1


def is_torus_link_relation(rel):
    # if rel == a^n b^m
    syls = get_syls(rel)
    return len(syls) == 2


def is_milley_relation(rel):
    # Lemma 4.2 of Milley's 2008 paper:
    # a^n b^m a^(-k) b^m
    # OR
    # a^n b^m a^n b^(-k)

    syls = get_syls(rel)

    if len(syls) != 4:
        return False

    [P, Q, R, S] = syls
    if Q == S and P[0].lower() == R[0].lower():
        return True
    if P == R and Q[0].lower() == S[0].lower():
        return True

    return False


def is_four_syllable_relation(rel):
    # if rel == a^p b^q a^r b^s

    syls = get_syls(rel)
    lets = [syl[0].lower() for syl in syls]

    if len(syls) != 4:
        return False

    a, b, c, d = lets
    if a == c and b == d:
        return True

    return False


# working with groups


def has_cyclic_free_factor(G, verbose):
    gens = G.generators()
    rels = G.relators()

    # ZZ
    for gen in gens:
        if all(gen not in rel for rel in rels):
            if verbose > 12: print(str(G), "has ZZ as free factor")
            return True

    # ZZ/nZZ
    for rel in rels:
        if is_cyclic_relation(rel):
            # get the lucky generator
            a = rel[0]
            # and make sure it does not appear elsewhere.
            rels_other = [relo for relo in rels if relo != rel]
            if all(a not in relo and a.swapcase() not in relo for relo in rels_other):
                if verbose > 12: print(str(G), "has finite cyclic free factor")
                return True

    return False


def is_free_product(G, verbose):
    """
    Given a snappy group G, returns True if G is obviously a free
    product.
    
    In more detail: Suppose that G = \group{X}{R}. Suppose that X = Y
    \sqcup Z and R = S \sqcup T are partitions so that (i) Y and Z are
    non-empty, (ii) the generators of Y do not appear in S, and (iii)
    the generators of Z do not appear in T.  Then G is isomorphic to
    the free product of \group{Y}{S} and \group{Z}{T}.
    """
    gens = G.generators()
    rels = G.relators()

    # free groups are free products
    if len(rels) == 0:
        return True

    syls_list = [get_syls(rel) for rel in rels]
    letters_list = [set(syl[0].lower() for syl in syls) for syls in syls_list]

    # A quick sketch of the algorithm.  Consider the hypergraph where
    # vertices are generators and we have one hyperedge {a, b, c...}
    # for each relation (if a^{-1} appears in a relation we instead
    # place a in the hyperedge).  We now compute the connected
    # component of the first generator.  If this not all of the
    # generators, return True.

    empty = set()
    amoeba = set([gens[0]])
    while any(amoeba.intersection(letters) != empty for letters in letters_list):
        # absorb
        for letters in letters_list:
            if amoeba.intersection(letters) != empty:
                amoeba = amoeba.union(letters)
        # update
        letters_list = [letters for letters in letters_list if not letters.issubset(amoeba)]
    if len(amoeba) < len(gens):
        if verbose > 12: print(str(G), "splits as free product")
        return True
    return False


def is_torus_link_group_quotient(G, verbose):
    # Add a proof here.

    gens = G.generators()
    rels = G.relators()

    if len(gens) == 2 and any(is_torus_link_relation(rel) for rel in rels):
        if verbose > 12: print(str(G), "has torus link relation")
        return True

    return False


def is_milley_group_quotient(G, verbose):
    # Lemma 4.2 of Milley's paper says that if G has two generators a, b that
    # satisfy the relation a^n b^m a^(-k) b^m = 1, then [a^(n+k),b^m] = 1.
    # This means G cannot be a hyperbolic 3-manifold group: if it was, the
    # two generators would stabilize the same line or horoball.

    gens = G.generators()
    rels = G.relators()

    if len(gens) == 2 and any(is_milley_relation(rel) for rel in rels):
        if verbose > 12: print(str(G), "has milley relation")
        return True

    return False


def is_four_syllable_group_quotient(G, verbose):
    # A lemma of Futer-Gabai-Yarmola says that if G is a torsion-free
    # Kleinian group generated by a, b, where a^p b^q a^r b^s = 1, then
    # G is elementary.
    # The lemma will appear in a future paper. The proof is not hard; it
    # is mainly a computation using right-angled hexagons.

    gens = G.generators()
    rels = G.relators()

    if len(gens) == 2 and any(is_four_syllable_relation(rel) for rel in rels):
        if verbose > 12: print(str(G), "has four-syllable relation")
        return True

    return False


# translating from manifolds to groups


def is_connect_sum(N, verbose):
    if verbose > 12: print(N, "entering is_connect_sum")
    G = N.fundamental_group()
    if len(G.generators()) < 2:
        # cyclic fundamental group, so not a connect sum
        return False
    return is_free_product(G, verbose)


def is_torus_link_filling(N, verbose):
    if verbose > 12: print(N, "entering is_torus_link_filling")
    G = N.fundamental_group()
    return is_torus_link_group_quotient(G, verbose)


def is_milley_manifold_filling(N, verbose):
    if verbose > 12: print(N, "entering is_milley_manifold_filling")
    G = N.fundamental_group()
    return is_milley_group_quotient(G, verbose)


def is_four_syllable_manifold_filling(N, verbose):
    if verbose > 12: print(N, "entering is_four_syllable_manifold_filling")
    G = N.fundamental_group()
    return is_four_syllable_group_quotient(G, verbose)


def has_lens_space_summand(N, verbose):
    # We allow sphere and disk bundles over circles as 'lens spaces'
    if verbose > 12: print(N, "entering has_lens_space_summand")
    G = N.fundamental_group()
    return has_cyclic_free_factor(G, verbose)


# the calling function


def is_exceptional_due_to_fundamental_group(N, tries, verbose):
    # Tries a few sanity checks that imply that N is a non-hyperbolic manifold.
    # Returns a boolean and the type (if any)
    if verbose > 12: print(N, "entering is_exceptional_due_to_fundamental_group")

    sigs = closed_isosigs(N, tries, max_tets = 50)
    # possibly add the best isosig to the table?

    for sig in sigs:
        P = snappy.Manifold(sig)
        G = P.fundamental_group()
        rels = G.relators()
        gens = G.generators()

        if len(gens) == 0:
            if verbose > 6: print(N, "has trivial fundamental group")
            return (True, "S3")

        if len(gens) == 1 and len(rels) == 0:
            if verbose > 6: print(N, "is S2 x S1")
            return (True, "S2 x S1")  ### Warning: expects closed manifold

        if len(rels) == 0:
            if verbose > 6: print(N, "has free fundamental group")
            return (True, "Free group")

        if len(gens) == 1 and len(rels) == 1:
            if verbose > 6: print(N, "is a lens space")
            return (True, "Lens")

        if has_lens_space_summand(N, verbose):
            if verbose > 6: print(N, "has lens or S2 x S1 summand")
            return (True, "Has lens or S2 x S1 summand")

        if is_connect_sum(N, verbose):
            if verbose > 6: print(N, "is a connect sum")
            return (True, "Connect sum")

        if is_torus_link_filling(N, verbose):
            if verbose > 6: print(N, "is torus link filling")
            return (True, "Torus link filling")

        if is_milley_manifold_filling(N, verbose):
            if verbose > 6: print(N, "is Milley manifold filling")
            return (True, "Milley manifold filling")

        if is_four_syllable_manifold_filling(N, verbose):
            if verbose > 6: print(N, "is four-syllable manifold")
            return (True, "Four-syllable manifold")

        ### TODO - detect centre???  Or deal with Seifert fibered
        ### fillings in some other way.

    return (None, None)


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
    Ms = snappy.Manifold(M)
    Nt = snappy.Manifold(N)
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
    abelianizations (sorted lexicographically for comparing).
    """

    subs = G.LowIndexSubgroupsFpGroup(deg)
    out = [[G.Index(H), H.AbelianInvariants()] for H in subs]
    out.sort()  # Sort lexicographically
    return subs, out


def profinite_data(G, subs, deg):
    """
    Given a Gap group G, and a list of finite-index subgroups subs
    (presumed to be all subgroups up to some index), computes
    invariants of the normal cores of subgroups whose index equals deg.
    Returns the following tuple of data for every subgroup H of index deg:
    [the index, the abelianization, the index of the normal core,
    and the abelianization of the normal core].
    Returns the set of these invariants, sorted lexicographically.
    """

    out = []
    for H in subs:
        if G.Index(H) == deg:
            K = G.FactorCosetAction(H).Kernel()
            out.append([G.Index(H), H.AbelianInvariants(), G.Index(K), K.AbelianInvariants()])
    out.sort()
    return out


def are_distinguished_by_normcore_homology(M, N, tries, verbose):
    """
    Given snappy manifolds M and N, tries to distinguish their
    fundamental groups using the abelianizations of finite-index subgroups
    and their normal cores. This uses GAP.

    For optimum speed, this routine should be used *after* trying
    are_distinguished_by_cover_homology, which takes advantage of faster
    cover enumeration in SnapPy 3.1.
    """

    verbose_print(verbose, 12, [M, N, "entering are_distinguished_by_normcore_homology"])

    GM = gap(M.fundamental_group().gap_string())
    GN = gap(N.fundamental_group().gap_string())
    degree_bound = min(tries, 6) # Hack: no degrees higher than 6

    # First, compute subgroups of GM and GN up to index degree_bound
    M_subs = GM.LowIndexSubgroupsFpGroup(degree_bound + 1)
    N_subs = GN.LowIndexSubgroupsFpGroup(degree_bound + 1)


    # for deg in range(1, degree_bound + 1):
    #     M_subs, M_data = subgroup_abels(GM, deg)
    #     N_subs, N_data = subgroup_abels(GN, deg)
    #     verbose_print(verbose, 8, [M, deg, M_data])
    #     verbose_print(verbose, 8, [N, deg, N_data])
    #     if M_data != N_data:
    #         verbose_print(verbose, 6, [M, N, "cover homology distinguishes in degree", deg])
    #         return True


    # Now, compute the homology and index of each normal core (for each degree separately)
    for deg in range(1, degree_bound + 1):
        M_invts = profinite_data(GM, M_subs, deg)
        N_invts = profinite_data(GN, N_subs, deg)
        verbose_print(verbose, 8, [M, deg, M_invts])
        verbose_print(verbose, 8, [N, deg, N_invts])
        if M_invts != N_invts:
            verbose_print(verbose, 6, [M, N, "homology of normal cores distinguishes in degree", deg])
            return True
        else:
            verbose_print(verbose, 6, [M, N, "homology of normal cores fails to distinguish in degree", deg])

    # We have failed
    return False


def are_distinguished_by_cover_homology(M, N, tries, verbose):
    """
    Given snappy manifolds M and N, tries to distinguish their
    fundamental groups using the first homology groups of finite-degree covers
    (ie, the abelianizations of finite-index subgroups). This routine is designed
    to take advantage of faster cover enumeration in Snappy 3.1.
    """

    verbose_print(verbose, 12, [M, N, "entering are_distinguished_by_cover_homology"])

    degree_bound = min(tries, 8) # Covers up to degree 8 should be acceptable

    for deg in range(1, degree_bound + 1):
        M_data = [Q.homology() for Q in M.covers(deg)]
        N_data = [Q.homology() for Q in N.covers(deg)]
        M_data.sort()
        N_data.sort()
        verbose_print(verbose, 8, [M, deg, M_data])
        verbose_print(verbose, 8, [N, deg, N_data])
        if M_data != N_data:
            verbose_print(verbose, 6, [M, N, "cover homology distinguishes in degree", deg])
            return True
        # Give a status update if (verbose*deg) is large
        verbose_print(verbose*deg, 36, [M, N, "cover homology up to degree", deg, "failed to distinguish"])

    # We have failed
    return False


def are_distinguished_by_covers(M, s, N, t, tries, verbose):
    """
    Given snappy manifolds M and N, and a pair of slopes s and t, tries to
    distinguish the fundamental groups of M(s) and N(t) using the abelianizations
    of finite-index subgroups.

    This proceeds in two steps. First, enumerate covers up to a fixed degree
    using SnapPy. This is very fast. If this does not succeed, then enumerate
    finite-index subgroups and their normal cores using GAP. This is slower, but
    produces a richer package of data.
    """

    verbose_print(verbose, 12, [M, s, N, t, "entering are_distinguished_by_covers"])
    Ms = snappy.Manifold(M)
    Nt = snappy.Manifold(N)
    Ms.dehn_fill(s)
    Nt.dehn_fill(t)
    if are_distinguished_by_cover_homology(Ms, Nt, tries, verbose):
        return True
    # elif are_distinguished_by_normcore_homology(Ms, Nt, tries, verbose):
    #     return True
    return False
