from snappy import OrientableCuspedCensus, Manifold
from cosmetic_mfds import check_mfds

import time
import sys

if __name__ == '__main__':
    cen = OrientableCuspedCensus(num_cusps = 1)
    f = open('bar.txt', 'w')
    fout = open('foo.txt', 'w')
    sys.stdout = fout
    out = check_mfds(cen[0:3])
    print(out, file=f)
