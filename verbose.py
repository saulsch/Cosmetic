#
# verbose
#

# Goal - a simple helper function for debugging.

def verbose_print(verbose, threshold, outputs):
    if verbose > threshold:
        print(" ".join(str(out) for out in outputs))
