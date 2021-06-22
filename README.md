# cosmetic
Checking if a list of knots (in the three-sphere) or of manifolds (typically hyperbolic) all satisfy the cosmetic surgery conjecture.

This code base requires SAGE version 9.2 or later

from importlib import reload

import snappy
import cosmetic_knots

Cen = snappy.CensusKnots()
Cen = snappy.AlternatingKnotExteriors()
Cen = snappy.CensusKnots()
remainder = cosmetic_knots.prune_using_invariants(Cen)

With the default settings, this	will make a report every 100 knots.
After dealing with all 1267 knots in the	census,	"remainder" should
contain the following names:

['K7_54', 'K8_94', 'K8_96', 'K9_446', 'K9_652', 'K9_659']

These six census knots do not come equipped	with diagrams, so are not
dealt with by the more powerful	diagrammatic invariants.

remainder = cosmetic_knots.check_knots(remainder, slope_method = "All")

Now remainder is empty - these six knots have no cosmetic surgery pairs.

Note that cosmetic_mfds is currently being developed.
(That is, it is broken.)
