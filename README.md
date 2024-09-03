# Cosmetic

The goal of this software is to check if a knot (in the three-sphere)
or a manifold (typically hyperbolic) satisfies the cosmetic surgery
conjecture.

### Prerequisites and installation

We work inside of SageMath.
We also assume that the user has snappy and regina installed inside of sage.
We are currently running sage 10.4, snappy 3.1, and regina 7.3.
You can find installation instructions for those programs here:

https://doc.sagemath.org/html/en/installation/  \
https://snappy.math.uic.edu/installing.html  \
https://github.com/3-manifolds/regina_wheels

To install Cosmetic via the command line type:

```
git clone https://github.com/saulsch/Cosmetic
```

### Example of usage

Inside of sage, in the github repository for Cosmetic type:

```
import snappy
import cosmetic_knots

Cen = snappy.CensusKnots()
remainder = cosmetic_knots.prune_using_invariants(Cen)
```

With the default settings, this will make a report every 100 knots.
The program can eliminate all 1267 knots in the census, so "remainder" 
will be empty. Note that computing diagrammatic invariants for some of 
these knots requires the exterior_to_link() function recently added to SnapPy.

The program can also exclude cosmetic surgeries on these knots
using hyperbolic methods.
```
remainder = cosmetic_knots.check_knots(Cen, slope_method='FPS')
```

Again, the remainder is empty: all 1267 knots have been eliminated.

One can also check manifolds instead of knots.

```
import snappy
import cosmetic_mfds

Cen = snappy.OrientableCuspedCensus(num_cusps = 1)
Cen = Cen[:10]
out = cosmetic_mfds.check_mfds(Cen)
```

Now out should be a pair of empty lists, as there are no pairs of
slopes contradicting either conjecture.

The code can also check for chirally cosmetic surgeries as well as for
common fillings.  You can find the documention as follows:

```
cosmetic_mfds.check_mfds?
cosmetic_mfds.check_cosmetic?
cosmetic_mfds.check_list_for_common_fillings?
```