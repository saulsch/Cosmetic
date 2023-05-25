#
# dunfield.py
#

import regina
import snappy
import re
import networkx as nx

from verbose import verbose_print

# This code has its origins in Dunfield's paper on exceptional slopes:

# https://dataverse.harvard.edu/file.xhtml?persistentId=doi:10.7910/DVN/6WNVG0/0X6FYV&version=1.0

# Some hacking has taken place. Most significantly, we have updated a lot of commands
# to interact with Regina 7.0 rather than 6.0.

################

# Code to prove a manifold is hyperbolic.  


def all_positive(manifold):
    return manifold.solution_type() == 'all tetrahedra positively oriented'

def find_positive_triangulation(manifold, tries = 3, verbose = 2):
    verbose_print(verbose, 12, [manifold, "entering find_positive_triangulation"])

    M = snappy.Manifold(manifold)
    for i in range(tries):
        if all_positive(M):
            verbose_print(verbose, 20, [M, "found a positive triangulation"])
            return M
        else:
            M.randomize()
    try: # this fails in verify_mt_action, sometimes
        verbose_print(verbose, 12, [M, "trying to drill and fill"])
        for d in M.dual_curves():
            X = M.drill(d)
            X = X.filled_triangulation()
            X.dehn_fill((1,0),-1)
            for i in range(tries):
                if all_positive(X):
                    return X
                X.randomize()
    except snappy.SnapPeaFatalError: 
        print(M, "we failed to drill and fill... why?")
        raise
    
    # In the closed case, here is another trick.
    verbose_print(verbose, 12, [M, "trying to drill and fill an edge"])

    if all(not c for c in M.cusp_info('is_complete')):
        for i in range(tries):
            # Drills out a random edge
            X = M.__class__(M.filled_triangulation())
            if all_positive(X):
                return X
            M.randomize()

    # everything has failed
    verbose_print(verbose, 10, [M, "positive triangulation fail"])

    return None
            
def verify_hyperbolic_basic(manifold, tries = 3, verbose = 2):
    verbose_print(verbose, 12, [manifold, "entering verify_hyperbolic_basic"])
    M = find_positive_triangulation(manifold, tries = tries, verbose = verbose)
    if M is not None:
        for i in range(tries):
            prec = 53*(2**i) # this used to go to 1000.  Now it goes to 11. 
            try:
                verbose_print(verbose, 12, [M, "try to verify_hyperbolicity at precision", prec])
                if M.verify_hyperbolicity(bits_prec=prec)[0]:
                    verbose_print(verbose, 12, [M, "verified hyperbolic"])
                    return True
            except RuntimeError:
                verbose_print(verbose, 12, [M, "had a RuntimeError"])
                print(M, 'Treating exception in verify code as a failure')
    return False

def verify_hyperbolic_basic_with_volume(manifold, tries = 3, verbose = 2):
    verbose_print(verbose, 12, [manifold, "entering verify_hyperbolic_basic_with_volume"])
    M = find_positive_triangulation(manifold, tries = tries, verbose = verbose)
    if M is not None:
        for i in range(tries):
            prec = 53*(2**i) # this used to go to 1000.  Now it goes to 11. 
            try:
                verbose_print(verbose, 12, [M, "try to verify_hyperbolicity at precision", prec])
                if M.verify_hyperbolicity(bits_prec = prec)[0]:
                    verbose_print(verbose, 12, [M, "verified hyperbolic"])
                    return (True, M.volume(verified = True, bits_prec = prec))
            except RuntimeError:
                verbose_print(verbose, 12, [M, "had a RuntimeError"])
                print(M, 'Treating exception in verify code as a failure')
    return (False, None)

def is_hyperbolic(manifold, tries = 10, verbose = 2):
    verbose_print(verbose, 12, [manifold, "entering is_hyperbolic"])

    if verify_hyperbolic_basic(manifold, tries = tries, verbose=verbose):
        verbose_print(verbose, 12, [manifold, "verify_hyperbolic_basic worked."])
        return True
    else:
        for d in range(2, min(tries, 8)):
            verbose_print(verbose, 12, [manifold, "trying cover of degree", d])
            for C in manifold.covers(d):
                if verify_hyperbolic_basic(C, tries = tries, verbose=verbose):
                    verbose_print(verbose, 12, [manifold, C, "covers plus verify_hyperbolic_basic worked."])
                    verbose_print(verbose, 12, ["covering degree is", d])
                    return True
    return False

                
def is_hyperbolic_with_volume(manifold, tries = 10, verbose = 2):
    verbose_print(verbose, 12, [])
    if verbose > 12:
        print(manifold, "entering is_hyperbolic_with_volume")

    is_hyp, vol = verify_hyperbolic_basic_with_volume(manifold, tries = tries, verbose = verbose)
        
    if is_hyp:
        verbose_print(verbose, 12, [])
        if verbose > 12:
            print(manifold, "verify_hyperbolic_basic_with_volume worked.")
        return (is_hyp, vol)
    else:
        for d in range(2, min(tries, 8)):
            for C in manifold.covers(d):
                verbose_print(verbose, 12, [])
                if verbose > 12:
                    print("trying cover of degree", d)
                is_hyp, vol = verify_hyperbolic_basic_with_volume(C, tries = tries, verbose = verbose)
                if is_hyp:
                    verbose_print(verbose, 12, [manifold, "covers plus verify_hyperbolic_basic_with_volume worked."])
                    verbose_print(verbose, 12, ["covering degree is", d])
                    return (is_hyp, vol/d)
    return (False, None)

                
###########################

# Provides functions for working with Regina (with a little
# help from SnapPy) to:

# 1. Give a standard name ("identify") manifolds, especially Seifert and
#    graph manifolds.

# 2. Find essential tori.

# 3. Try to compute the JSJ decomposition.

def appears_hyperbolic(M):
    acceptable = ['all tetrahedra positively oriented',
                  'contains negatively oriented tetrahedra']
    return M.solution_type() in acceptable and M.volume() > 0

'''
The following seems to be unnecessary now that Regina 7.0 returns lists

def children(packet):
    child = packet.firstChild()
    while child:
        yield child
        child = child.nextSibling()
'''

def to_regina(data):
    if hasattr(data, '_to_string'):
        data = data._to_string()
    if isinstance(data, str):
        if data.find('(') > -1:
            data = closed_isosigs(data)[0]
        return regina.Triangulation3(data)
    assert isinstance(data, regina.Triangulation3)
    return data

def extract_vector(surface):
    """
    Extract the raw vector of the (almost) normal surface in Regina's
    NS_STANDARD coordinate system.
    """
    S = surface
    T = S.triangulation()
    n = T.countTetrahedra()
    ans = []
    for i in range(n):
        for j in range(4):
            ans.append(S.triangles(i, j))
        for j in range(3):
            ans.append(S.quads(i, j))
    A = regina.NormalSurface(T, regina.NS_STANDARD, ans)
    assert A.sameSurface(S)
    return ans

def haken_sum(S1, S2):
    T = S1.triangulation()
    assert S1.locallyCompatible(S2)
    v1, v2 = extract_vector(S1), extract_vector(S2)
    sum_vec = [x1 + x2 for x1, x2 in zip(v1, v2)]
    A = regina.NormalSurface(T, regina.NS_STANDARD, sum_vec)
    assert S1.locallyCompatible(A) and S2.locallyCompatible(A)
    assert S1.eulerChar() + S2.eulerChar() == A.eulerChar()
    return A

def census_lookup(regina_tri):
    """
    Should the input triangulation be in Regina's census, return the
    name of the manifold, dropping the triangulation number.
    """
    hits = regina.Census.lookup(regina_tri)
    # The following is a Regina 6.0 command, deprecated in Regina 7.0
    # hit = hits.first()
    if len(hits) == 0:
        return None
    hit = hits[0]
    if hit is not None:
        name = hit.name()
        match = re.search(r"(.*) : #\d+$", name)
        if match:
            return match.group(1)
        else:
            return match

def standard_lookup(regina_tri):
    match = regina.StandardTriangulation.recognise(regina_tri)
    if match:
        return match.manifold()

def closed_isosigs(snappy_manifold, tries = 20, max_tets = 50):
    """
    Generate a slew of 1-vertex triangulations of a closed manifold
    using SnapPy.
    
    >>> M = snappy.Manifold('m004(1,2)')
    >>> len(closed_isosigs(M, tries=5)) > 0
    True
    """
    M = snappy.Manifold(snappy_manifold)
    assert set(M.cusp_info('complete?')) == {False}
    surgery_descriptions = [snappy.Manifold(M)]

    try:
        for curve in M.dual_curves():
            N = M.drill(curve)
            N.dehn_fill((1,0), 1)
            surgery_descriptions.append(N.filled_triangulation([0]))
    except snappy.SnapPeaFatalError:
        pass

    if len(surgery_descriptions) == 1:
        # Try again, but unfill the cusp first to try to find more
        # dual curves.
        try:
            filling = M.cusp_info(0).filling
            N = snappy.Manifold(M)
            N.dehn_fill((0, 0), 0)
            N.randomize()
            for curve in N.dual_curves():
                D = N.drill(curve)
                D.dehn_fill([filling, (1,0)])
                surgery_descriptions.append(D.filled_triangulation([0]))
        except snappy.SnapPeaFatalError:
            pass

    ans = set()
    for N in surgery_descriptions:
        for i in range(tries):
            T = N.filled_triangulation()
            if T._num_fake_cusps() == 1:
                n = T.num_tetrahedra()
                if n <= max_tets:
                    ans.add((n, T.triangulation_isosig(decorated=False)))
            N.randomize()

    return [iso for n, iso in sorted(ans)]

def best_match(matches):
    """
    Prioritize the most concise description that Regina provides to
    try to avoid things like the Seifert fibered space of a node being
    a solid torus or having several nodes that can be condensed into a
    single Seifert fibered piece.
    """
    
    def score(m):
        if isinstance(m, regina.SFSpace):
            s = 0
        elif isinstance(m, regina.GraphLoop):
            s = 1
        elif isinstance(m, regina.GraphPair):
            s = 2
        elif isinstance(m, regina.GraphTriple):
            s = 3
        elif m is None:
            s = 10000
        else:
            s = 4
        return (s, str(m))
    return min(matches, key=score)


def identify_with_torus_boundary(regina_tri):
    """
    Use the combined power of Regina and SnapPy to try to give a name
    to the input manifold.
    """
    
    kind, name = "unknown", None
    
    P = regina.Triangulation3(regina_tri) # a clone of the triangulation
    P.finiteToIdeal()
    P.intelligentSimplify()
    M = snappy.Manifold(P.isoSig())
    M.simplify()
    if appears_hyperbolic(M):
        for i in range(100):
            if M.solution_type() == 'all tetrahedra positively oriented':
                break
            M.randomize()
        
        if not M.verify_hyperbolicity(bits_prec=100):
            raise RuntimeError('Cannot prove hyperbolicity for ' +
                               M.triangulation_isosig())
        kind = 'hyperbolic'
        ids = M.identify()
        if ids:
            name = ids[0].name()
    else:
        match = standard_lookup(regina_tri)
        if match is None:
            Q = regina.Triangulation3(P)
            Q.idealToFinite()
            Q.intelligentSimplify()
            match = standard_lookup(Q)
        if match is not None:
            kind = match.__class__.__name__
            name = str(match)
        else:
            name = P.isoSig()
    return kind, name


def is_toroidal(regina_tri):
    """
    Checks for essential tori and returns the pieces of the
    associated partial JSJ decomposition.
    
    >>> T = to_regina('hLALAkbccfefgglpkusufk')  # m004(4,1)
    >>> is_toroidal(T)[0]
    True
    >>> T = to_regina('hvLAQkcdfegfggjwajpmpw')  # m004(0,1)
    >>> is_toroidal(T)[0]
    True
    >>> T = to_regina('nLLLLMLPQkcdgfihjlmmlkmlhshnrvaqtpsfnf')  # 5_2(10,1)
    >>> T.isHaken()
    True
    >>> is_toroidal(T)[0]
    False

    Note: currently checks all fundamental normal tori; possibly
    the theory lets one just check *vertex* normal tori.
    """
    T = regina_tri
    assert T.isZeroEfficient()
    # got rid of regina.NormalSurfaces.enumerate
    surfaces = regina.NormalSurfaces(T, regina.NS_QUAD, regina.NS_FUNDAMENTAL)
    for i in range(surfaces.size()):
        S = surfaces.surface(i)
        if S.eulerChar() == 0:
            if not S.isOrientable():
                S = S.doubleSurface()
            assert S.isOrientable()
            X = S.cutAlong()
            X.intelligentSimplify()
            # The following is Regina 6.0 code, deprecated in version 7.0
            # X.splitIntoComponents()
            # pieces = list(children(X))
            pieces = X.triangulateComponents()
            if all(not C.hasCompressingDisc() for C in pieces):
                ids = [identify_with_torus_boundary(C) for C in pieces]
                return (True, sorted(ids))
                
    return (False, None)


def decompose_along_tori(regina_tri):
    """
    First, finds all essential normal tori in the manifold associated
    with fundamental normal surfaces.  Then takes a maximal disjoint
    collection of these tori, namely the one with the fewest tori
    involved, and cuts the manifold open along it.  It tries to
    identify the pieces, removing any (torus x I) components. 

    Returns: (has essential torus, list of pieces)

    Note: This may fail to be the true JSJ decomposition. There might be
    unrecognized (torus x I)'s in the list of pieces and it might well be
    possible to amalgamate some of the pieces into a single SFS.
    """
    
    T = regina_tri
    assert T.isZeroEfficient()
    assert T.isConnected() # We will be counting components below
    incompress_tori = []
    # got rid of regina.NormalSurfaces.enumerate
    surfaces = regina.NormalSurfaces(T, regina.NS_QUAD, regina.NS_FUNDAMENTAL)
    for i in range(surfaces.size()):
        S = surfaces.surface(i)
        if S.eulerChar() == 0:
            if not S.isOrientable():
                S = S.doubleSurface()
            assert S.isOrientable()
            X = S.cutAlong()
            X.intelligentSimplify()
            # The following is Regina 6.0 code, deprecated in version 7.0
            # X.splitIntoComponents()
            # pieces = list(children(X))
            pieces = X.triangulateComponents()
            if all(not C.hasCompressingDisc() for C in pieces):
                incompress_tori.append(S)

    if incompress_tori == []:
        return False, None
    
    # Compute disjointness graph.
    D = nx.Graph()
    for a, A in enumerate(incompress_tori):
        for b, B in enumerate(incompress_tori):
            if a < b:
                if A.disjoint(B):
                    D.add_edge(a, b)

    # Build A, the union of a clique of disjoint tori such that any torus disjoint from A
    # is parallel into A.
    cliques = list(nx.find_cliques(D))
    if len(cliques) == 0:
        clique = [0]
    else:
        clique = min(cliques, key=len)
    clique = [incompress_tori[c] for c in clique]
    num_tori = len(clique)
    A = clique[0]
    for B in clique[1:]:
        A = haken_sum(A, B)

    X = A.cutAlong()
    X.intelligentSimplify()
    # The following is Regina 6.0 code, deprecated in version 7.0
    # X.splitIntoComponents()
    # pieces = list(children(X))
    pieces = X.triangulateComponents()
    ids = [identify_with_torus_boundary(C) for C in pieces]

    # Count products. If this is less than the number of tori that we cut along,
    # then at least one torus is not boundary-parallel
    num_products = len([i for i in ids if i[1] in ('SFS [A: (1,1)]', 'A x S1')])
    # The following is Regina 6.0 code, deprecated in version 7.0
    # if len(T.boundaryComponents()) > 0 and (num_products >= num_tori):
    if T.boundaryComponents().size() > 0 and (num_products >= num_tori): 
        # All tori are boundary-parallel
        toroidal = False
    else:
        toroidal = True
    
    # Remove products
    pruned_ids = [i for i in ids if i[1] not in ('SFS [A: (1,1)]', 'A x S1')]
    # But if nothing is left, then keep one product
    if pruned_ids == []:
        pruned_ids = ids[:1]
    
    return (toroidal, sorted(pruned_ids))


def identify_with_bdy_from_isosig(data):
    """
    Given the isosig of an ideal triangulation, use the combined 
    power of Regina and SnapPy to try to give a name to the input 
    manifold. Decompose along tori, if necessary.
    
    Also works if handed a snappy Manifold.
    """
    
    kind, name = "unknown", None

    # If handed an isosig, throw away the boundary framing
    if isinstance(data, str):
        parts = iso.split("_")
        data = parts[0]
    
    P = to_regina(data)
    P.intelligentSimplify()
    M = snappy.Manifold(data)
    M.simplify()
    if appears_hyperbolic(M):
        for i in range(100):
            if M.solution_type() == 'all tetrahedra positively oriented':
                break
            M.randomize()
        
        if not M.verify_hyperbolicity(bits_prec=100):
            raise RuntimeError('Cannot prove hyperbolicity for ' +
                               M.triangulation_isosig())
        kind = 'hyperbolic'
        ids = M.identify()
        if ids:
            name = ids[0].name()
            return kind, name
    else:
        match = standard_lookup(P)
        if match is None:
            P.idealToFinite()
            P.intelligentSimplify()
            match = standard_lookup(P)
        if match is not None:
            kind = match.__class__.__name__
            name = str(match)
            return kind, name
        if match is None:
            toroidal, pieces = decompose_along_tori(P)
            if toroidal:
                kind = 'toroidal'
                name = str(pieces)
            else:
                # If atoroidal, there should be only one piece
                assert len(pieces) == 1
                kind = pieces[0][0]
                name = pieces[0][1]
            return kind, name

    # At this point, we have failed. Return the only data available.
    name = P.isoSig()
    return kind, name
    

def regina_name(closed_snappy_manifold, tries = 100, max_tets = 25):
    """
    >>> regina_name('m004(1,0)')
    'S3'
    >>> regina_name('s006(-2, 1)')
    'SFS [A: (5,1)] / [ 0,-1 | -1,0 ]'
    >>> regina_name('m010(-1, 1)')
    'L(3,1) # RP3'
    >>> regina_name('m022(-1,1)')
    'SFS [S2: (3,2) (3,2) (4,-3)]'
    >>> regina_name('v0004(0, 1)')
    'SFS [S2: (2,1) (4,1) (15,-13)]'
    >>> regina_name('m305(1, 0)')
    'L(3,1) # RP3'
    """
    M = snappy.Manifold(closed_snappy_manifold)
    isosigs = closed_isosigs(M, tries = tries, max_tets = max_tets)
    if len(isosigs) == 0:
        return
    T = to_regina(isosigs[0])
    if T.isIrreducible():
        if T.countTetrahedra() <= max_tets: # This used to be 11 - a magic number.  We may regret changing it...
            for i in range(3):
                T.simplifyExhaustive(i)
                name = census_lookup(T)
                if name is not None:
                    return name
            
        matches = [standard_lookup(to_regina(iso)) for iso in isosigs]
        match = best_match(matches)
        if match is not None:
            return str(match)
    else:
        # The following is Regina 6.0 code, deprecated in version 7.0
        # T.connectedSumDecomposition()
        # pieces = list(children(T))
        pieces = T.summands()
        if len(pieces) == 1:
            return census_lookup(pieces[0])
        pieces = [regina_name(P) for P in pieces]
        if None not in pieces:
            return ' # '.join(sorted(pieces))
