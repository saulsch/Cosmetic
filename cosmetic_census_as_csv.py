import csv
import sys
import traceback

import snappy.geometric_structure.geodesic
from snappy import OrientableCuspedCensus

from cosmetic_mfds import check_mfds


snappy.geometric_structure.geodesic.constants.graph_trace_max_steps = 1000


def print_usage():
    script_name = "cosmetic_census_as_csv.py"
    print(f"Usage: sage {script_name} NUM_TETS CHUNK_SIZE CHUNK_INDEX")
    print()
    print("       Writes CHUNK_SIZE manifolds to")
    print("       cosmetic_census_$(NUM_TETS)tets_$(FIRST_INDEX).csv, starting with")
    print("       manifold FIRST_INDEX=CHUNK_SIZE * CHUNK_INDEX.")
    print("       Writes the header to cosmetic_census_$(NUM_TETS)tets_000000.csv.")
    print()
    print("       Can be run with:")
    print(f"           1. parallel -j 4 sage {script_name} 11 100 -- `seq 0 4829`")
    print(f'           2. parallel -j 4 "sage {script_name} 11 100 {{}}" ::: `seq 0 4829`')
    print()
    print("       Note that there are two incompatible versions of parallel.")
    print("       Use 1. for parallel from the moreutils package on Linux (e.g., Ubuntu)")
    print("       or Homebrew (macOS).")
    print("       Use 2. for parallel from the package called parallel.")
    print()
    print("       -j/--jobs is the number of parallel processes.")
    print()
    print("       After running, combine the chunks into a spreadsheet-compatible CSV:")
    print("           cat cosmetic_census_11tets_*.csv > cosmetic_census_11tets.csv")


def main():
    try:
        num_tets, chunk_size, chunk_index = map(int, sys.argv[1:])
        if len(sys.argv) != 4:
            raise ValueError
    except ValueError:
        print_usage()
        return 1

    first_index = chunk_index * chunk_size
    output_path = f"cosmetic_census_{num_tets:02d}tets_{first_index:06d}.csv"

    with open(output_path, "w", newline="") as output_file:
        writer = csv.writer(output_file)
        if chunk_index == 0:
            writer.writerow(("Manifold", "Status", "Undistinguished", "Exception"))

        census = OrientableCuspedCensus(tets=num_tets, num_cusps=1)
        for manifold in census[first_index:first_index + chunk_size]:
            print(f"Working on {manifold}", flush=True)
            try:
                amphichiral_undistinguished, bad_undistinguished = check_mfds(
                    [manifold], verbose=7)
                if not bad_undistinguished and not amphichiral_undistinguished:
                    writer.writerow((manifold, "Ok", "", ""))
                else:
                    info = repr(amphichiral_undistinguished) + repr(bad_undistinguished)
                    writer.writerow((manifold, "Failed", info, ""))
            except Exception as error:
                writer.writerow((manifold, "Failed", "", repr(error)))
                traceback.print_exc()
            output_file.flush()

    return 0


if __name__ == "__main__":
    sys.exit(main())
