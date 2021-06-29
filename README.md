# Cosmetic

The goal of this software is to check if a knot (in the three-sphere)
or a manifold (typically hyperbolic) satisfies the cosmetic surgery
conjecture.

We work inside of SageMath (as of this writing version 9.2).
We assume that the user has snappy and regina installed inside of sage.  
You can find installation instructions for those programs here: 

https://doc.sagemath.org/html/en/installation/
https://snappy.math.uic.edu/installing.html
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

With the default settings, this	will make a report every 100 knots.
After dealing with all 1267 knots in the	census,	"remainder" should 
contain the following names:

```
['K7_54', 'K8_94', 'K8_96', 'K9_446', 'K9_652', 'K9_659']
```

These six census knots do not come equipped	with diagrams, so are not
dealt with by	diagrammatic invariants.  Instead we can use hyperbolic
geometry to eliminate these knots.

```
remainder = cosmetic_knots.check_knots(remainder, slope_method = "All")
```

Now remainder is empty - these six knots have no cosmetic surgery pairs.

### In progress

The code in cosmetic_mfds is currently being developed.
