from snappy.geometric_structure.geodesic import constants
# This will be the default value in upcoming SnapPy versions 3.4.
constants.graph_trace_max_steps = 1000

def matthias_surgery_description(M):
    G = M.fundamental_group(False)
    real_len, g = min((real_len, g) for g in G.generators() if (real_len := G.complex_length(g).real()) > 1e-6)
    if real_len > 0.4:
        return M
    try:
        N = M.drill_word(g, bits_prec = 1000)
    except:
        return M
    N.dehn_fill((1,0),-1)

    for i in range(1000):
        if N.solution_type() == 'all tetrahedra positively oriented':
            return N
        N.randomize()

    return M

def matthias_systole(M, cutoff = None):
    N = matthias_surgery_description(M)

    for bits_prec in [500, 1000, 5000]:
        try:
            L = N.length_spectrum_alt(count=1, max_len=cutoff, verified=True, bits_prec=bits_prec)
        except:
            continue

        if len(L) > 0:
            return L[0].length.real()
        elif cutoff is not None:
            return cutoff
        else:
            raise RuntimeError("Unexpected empty length spectrum")

    return None
