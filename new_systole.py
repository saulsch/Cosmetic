from snappy.geometric_structure.geodesic import constants
# This is the default value in the upcoming SnapPy versions 3.4.
constants.graph_trace_max_steps = 1000

min_len_for_drilling = 1e-6
max_len_for_drilling = 0.4
drilling_precision = 1000
randomization_tries = 1000
len_spec_precisions = [500, 1000, 5000]

def surgery_description(M):
    """
    Try to heuristically drill shortest geodesic and immediately fill it to
    obtain a surgery description which accelerates the length spectrum.
    """

    G = M.fundamental_group(False)
    real_len, g = min(
        (real_len, g)
        for g in G.generators()
        if (real_len := G.complex_length(g).real()) > min_len_for_drilling)
    if real_len > max_len_for_drilling:
        return M
    try:
        N = M.drill_word(g, bits_prec=drilling_precision)
    except:
        return M
    N.dehn_fill((1,0),-1)

    for i in range(randomization_tries):
        if N.solution_type() == 'all tetrahedra positively oriented':
            return N
        N.randomize()

    return M

def new_verified_systole(M, cutoff = None):
    """
    Compute a SnapPy Manifold M, tries to compute the verified systole
    of M as SageMath RealIntervalField.
    If cutoff (of type RealIntervalField) is given, it returns the
    verified min of the systole and cutoff instead.

    That is, specify cutoff for applications only interested in systoles
    shorter than the given cutoff.
    """

    N = surgery_description(M)

    for bits_prec in len_spec_precisions:
        try:
            L = N.length_spectrum_alt(
                count=1, max_len=cutoff, verified=True, bits_prec=bits_prec)
        except:
            continue

        if len(L) > 0:
            return L[0].length.real()
        elif cutoff is not None:
            return cutoff
        else:
            raise RuntimeError("Unexpected empty length spectrum")

    return None
