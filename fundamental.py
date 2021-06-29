#
# fundamental.py
#

# Goal - use the fundamental group to recognise a given three-manifold.

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
    return ((a, n), w[n:])


def get_syls(w):
    """                                                                         
    Given a word w, break it into syllables.                                    
    """
    syls = []
    while len(w) > 0:
        syl, w = get_first_syl(w)
        syls.append(syl)
    return syls


# Fundamental group


# Standing assumptions: relations have non-zero length.  Also,
# generators are letters.  (If there are more the 26 generators then
# something is very wrong in any case...) 

# Strings are not a commutative monoid, so the notation python uses is
# all wrong; it uses a + b for concatenation, instead of a*b, and uses
# a*n for powers, instead of a^n.  Silly computer scientists!

def is_cyclic_relation(rel):
    c = rel[0] 
    return rel == c*len(rel)


def is_torus_link_relation(rel):
    a = rel[0]
    b = rel[-1]
    return rel == a*rel.count(a) + b*rel.count(b)


def is_milley_relation(rel):
    # The relation from Lemma 4.2 of Milley's 2008 paper:
    # a^n b^m a^(-k) b^m
    # OR
    # a^n b^m a^n b^(-k)

    syls = get_syls(rel)

    if len(syls) != 4:
        return False

    [(a, p), (b, q), (c, r), (d, s)] = syls

    if (b, q) == (d, s) and a.lower() == c.lower():
        return True

    if (a, p) == (c, r) and b.lower() == d.lower():
        return True

    return False
    

def is_futer_relation(rel):
    # a^p b^q a^r b^s

    syls = get_syls(rel)

    if len(syls) != 4:
        return False

    [(a, p), (b, q), (c, r), (d, s)] = syls

    if a.lower() == c.lower() and b.lower() == d.lower():
        return True

    return False
    

def is_torus_link_group_quotient(G, verbose):
    # Add a proof here. 

    gens = G.generators()
    rels = G.relators()

    if len(gens) == 2 and any(is_torus_link_relation(rel) for rel in rels):
        if verbose > 12: print(str(G), 'has torus link relation')
        return True


def is_milley_group_quotient(G, verbose):
    # Lemma 4.2 of Milley's paper says that if generators a, b satisfy 
    # the relation a^n b^m a^(-k) b^m = 1, then [a^(n+k),b^m] = 1.
    # This means G cannot be a hyperbolic 3-manifold group: if it was, the
    # two generators would stabilize the same line or horoball, which would
    # mean that G is abelian. Contradiction.

    gens = G.generators()
    rels = G.relators()

    if len(gens) == 2 and any(is_milley_relation(rel) for rel in rels):
        if verbose > 12: print(str(G), 'has milley relation')
        return True


def is_futer_group_quotient(G, verbose):
    gens = G.generators()
    rels = G.relators()

    if len(gens) == 2 and any(is_futer_relation(rel) for rel in rels):
        if verbose > 12: print(str(G), 'has futer relation')
        return True


def is_torus_link_filling(M, verbose):
    if verbose > 12: print(M, 'entering is_torus_link_filling')
    G = M.fundamental_group()
    return is_torus_link_group_quotient(G, verbose)


def is_milley_manifold_filling(M, verbose):
    if verbose > 12: print(M, 'entering is_milley_manifold_filling')
    G = M.fundamental_group()
    return is_milley_group_quotient(G, verbose)


def is_futer_manifold_filling(M, verbose):
    if verbose > 12: print(M, 'entering is_futer_manifold_filling')
    G = M.fundamental_group()
    return is_futer_group_quotient(G, verbose)


def has_cyclic_free_factor(G, verbose):
    gens = G.generators()
    rels = G.relators()
    
    for rel in rels:
        # if rel is a power, say x^n, make sure that x and X appear nowhere else. 
        if is_cyclic_relation(rel) and all (rel == rel_prime for rel_prime in rels if (rel[0] in rel_prime or \
                                                                                       rel[0].swapcase() in rel_prime)):
            if verbose > 12: print(str(G), 'has cyclic free factor')
            return True
    

def has_lens_space_summand(N, verbose):
    if verbose > 12: print(N, 'entering has_lens_space_summand')
    G = N.fundamental_group()
    return has_cyclic_free_factor(G, verbose)
    

def is_exceptional_due_to_fundamental_group(N, tries, verbose):
    # Tries a few sanity checks that implies N is a non-hyperbolic manifold.
    # Returns a Boolean and the type (if any)
    if verbose > 12: print(N, 'entering is_exceptional_due_to_fundamental_group')
    for i in range(tries):
        P = N.filled_triangulation()
        ### possibly use the best isosig here.
        ### possibly add the best isosig to the table?
        G = P.fundamental_group()
        rels = G.relators()
        gens = G.generators()

        if len(gens) == 0:
            if verbose > 6: print(N, 'has trivial fundamental group')
            return (True, 'S3')

        if len(gens) == 1 and len(rels) == 0:
            if verbose > 6: print(N, 'is S2 x S1')
            return (True, 'S2 x S1')  ### Warning: expects closed manifold

        if len(rels) == 0:
            if verbose > 6: print(N, 'has free fundamental group')
            return (True, 'Free group')
    
        if len(gens) == 1 and len(rels) == 1:
            if verbose > 6: print(N, 'is a lens space')
            return (True, 'Lens')

        if has_lens_space_summand(N, verbose):
            if verbose > 6: print(N, 'has lens space summand')
            return (True, 'Has lens space summand')

        if is_torus_link_filling(N, verbose):
            if verbose > 6: print(N, 'is torus link filling')
            return (True, 'Torus link filling')

        if is_milley_manifold_filling(N, verbose):
            if verbose > 6: print(N, 'is Milley manifold filling')
            return (True, 'Milley manifold filling')

        if is_futer_manifold_filling(N, verbose):
            if verbose > -2: print(N, 'is Futer manifold filling')
            return (True, 'Futer manifold filling')

        N.randomize()

    return (None, None)
