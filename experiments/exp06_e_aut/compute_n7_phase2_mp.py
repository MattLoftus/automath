#!/usr/bin/env python3
"""
Phase 2 multiprocessing version: count automorphisms for each unique 2-order shape.
Reads multiplicity dict from JSON (produced by phase 1), computes aut counts in parallel.
"""
import json
import time
import sys
from multiprocessing import Pool, cpu_count
from itertools import permutations
from fractions import Fraction

N = 7

def encode_pi(pi, N):
    """Encode pi as a list[int] for fast access."""
    return list(pi)

def count_auts_for_shape(args):
    """Count auts for one 2-order shape."""
    bm, perms_flat = args
    # Extract pairs from bitmask
    pairs = []
    for k in range(N * N):
        if bm & (1 << k):
            pairs.append((k // N, k % N))
    n_pairs = len(pairs)

    # Reconstruct perms from flat
    perms_count = len(perms_flat) // N
    aut_count = 0
    for p_idx in range(perms_count):
        pi = perms_flat[p_idx * N : (p_idx + 1) * N]
        ok = True
        for i, j in pairs:
            if not (bm & (1 << (pi[i] * N + pi[j]))):
                ok = False
                break
        if ok:
            aut_count += 1
    return bm, aut_count


def main():
    print(f"Phase 2 (multiprocessing) for N={N}")
    print(f"  CPU cores available: {cpu_count()}")

    # Load multiplicity dict from Phase 1.
    print(f"  Loading multiplicity dict from phase1_data.json...")
    t0 = time.time()
    with open("phase1_data.json", "r") as f:
        data = json.load(f)
    multiplicity = {int(k): v for k, v in data["multiplicity"].items()}
    n_pairs = data["n_pairs"]
    print(f"  Loaded {len(multiplicity):,} unique 2-orders, "
          f"n_pairs={n_pairs:,} (took {time.time()-t0:.1f}s)")

    # Build perms list once.
    perms = list(permutations(range(N)))
    perms_flat = [v for p in perms for v in p]

    # Distribute shapes across worker processes.
    print(f"  Spawning Pool with {cpu_count()} workers...")
    t0 = time.time()
    args_list = [(bm, perms_flat) for bm in multiplicity.keys()]

    with Pool(cpu_count()) as pool:
        # Use imap_unordered for streaming progress
        n_unique = len(multiplicity)
        aut_results = {}
        for i, (bm, ac) in enumerate(pool.imap_unordered(count_auts_for_shape, args_list, chunksize=1000)):
            aut_results[bm] = ac
            if i % 50000 == 0:
                elapsed = time.time() - t0
                done = (i + 1) / n_unique
                eta = elapsed / max(done, 1e-9)
                sys.stdout.write(
                    f"\r  shape {i+1}/{n_unique:,} ({done*100:.1f}%), "
                    f"elapsed {elapsed:.1f}s / ETA {eta:.0f}s"
                )
                sys.stdout.flush()
    print()

    print(f"  Phase 2 done in {time.time()-t0:.1f}s")

    # Sum up.
    total = sum(multiplicity[bm] * aut_results[bm] for bm in multiplicity)
    E_aut = Fraction(total, n_pairs)
    print()
    print("=" * 70)
    print(f"  RESULT for N={N}:")
    print(f"    Sum |Aut| over (σ, τ) pairs: {total:,}")
    print(f"    E[|Aut|]                    = {E_aut} = {float(E_aut):.6f}")
    print(f"    unique 2-order shapes:        {len(multiplicity):,}")
    print(f"    A001035(7) = 6,129,859 labeled posets; "
          f"diff (dim>2): {6129859 - len(multiplicity):,}")

    # Save
    with open("result_N7.json", "w") as f:
        json.dump({
            "N": N,
            "sum_aut": total,
            "n_pairs": n_pairs,
            "E_aut_numerator": E_aut.numerator,
            "E_aut_denominator": E_aut.denominator,
            "n_unique_2orders": len(multiplicity),
        }, f, indent=2)
    print()
    print("Result saved to result_N7.json")


if __name__ == "__main__":
    main()
