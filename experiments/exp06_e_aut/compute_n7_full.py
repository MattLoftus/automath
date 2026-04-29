#!/usr/bin/env python3
"""
N=7 enumeration of E[|Aut|] with parallelized Phase 2.

Phase 1: enumerate all (sigma, tau) pairs, encode each 2-order as a 49-bit
mask, build multiplicity dict. ~80s single-thread.

Phase 2: count automorphisms per unique 2-order shape using a multiprocessing
Pool. With 14 cores on M4 Pro, ~30 min for ~5.9M unique shapes.

Total expected: ~30-35 min.
"""
from itertools import permutations
from fractions import Fraction
from multiprocessing import Pool, cpu_count
import time
import sys
import json
import os

N = 7

# Build perms once at module load so worker processes inherit it.
PERMS = [list(p) for p in permutations(range(N))]


def count_auts_for_shape(bm):
    """Worker: count permutations preserving the 2-order encoded as bm."""
    pairs = [(k // N, k % N) for k in range(N * N) if bm & (1 << k)]
    aut_count = 0
    for pi in PERMS:
        ok = True
        for i, j in pairs:
            if not (bm & (1 << (pi[i] * N + pi[j]))):
                ok = False
                break
        if ok:
            aut_count += 1
    return bm, aut_count


def main():
    print(f"Computing E[|Aut|] for N={N}")
    print(f"  Sym(N) size: {len(PERMS):,}")
    print(f"  (sigma, tau) pairs: {len(PERMS)**2:,}")
    print(f"  CPU cores: {cpu_count()}")

    # ---- Phase 1: encode all (sigma, tau) pairs as bitmasks ----
    print()
    print("Phase 1: encoding all (sigma, tau) pairs as bitmasks...")
    t0 = time.time()
    multiplicity = {}

    for idx, sigma in enumerate(PERMS):
        for tau in PERMS:
            bm = 0
            for i in range(N):
                si = sigma[i]
                ti = tau[i]
                for j in range(N):
                    if i != j and si < sigma[j] and ti < tau[j]:
                        bm |= 1 << (i * N + j)
            multiplicity[bm] = multiplicity.get(bm, 0) + 1
        if idx % 200 == 0:
            elapsed = time.time() - t0
            done = (idx + 1) / len(PERMS)
            eta = elapsed / max(done, 1e-9)
            sys.stdout.write(
                f"\r  σ {idx+1}/{len(PERMS)} ({done*100:.1f}%), "
                f"unique: {len(multiplicity):,}, "
                f"elapsed {elapsed:.0f}s / ETA {eta:.0f}s"
            )
            sys.stdout.flush()
    print()
    phase1_time = time.time() - t0
    print(f"  Phase 1 done in {phase1_time:.1f}s, "
          f"{len(multiplicity):,} unique 2-order shapes")

    # Save phase 1 data in case we need to resume.
    print(f"  Saving phase 1 data to phase1_data.pickle...")
    import pickle
    with open("phase1_data.pickle", "wb") as f:
        pickle.dump({"N": N, "multiplicity": multiplicity}, f)

    # ---- Phase 2: count autos per unique shape, multiprocessing ----
    print()
    print(f"Phase 2: counting automorphisms (multiprocessing)...")
    t0 = time.time()
    n_unique = len(multiplicity)
    keys = list(multiplicity.keys())

    aut_counts = {}
    n_workers = cpu_count()
    print(f"  Using {n_workers} worker processes; chunking by 1000")

    # imap_unordered for streaming progress
    with Pool(n_workers) as pool:
        for i, (bm, ac) in enumerate(
            pool.imap_unordered(count_auts_for_shape, keys, chunksize=200)
        ):
            aut_counts[bm] = ac
            if i % 25000 == 0 or i == n_unique - 1:
                elapsed = time.time() - t0
                done = (i + 1) / n_unique
                eta = elapsed / max(done, 1e-9)
                sys.stdout.write(
                    f"\r  shape {i+1:,}/{n_unique:,} ({done*100:.1f}%), "
                    f"elapsed {elapsed:.0f}s / ETA {eta:.0f}s"
                )
                sys.stdout.flush()
    print()
    phase2_time = time.time() - t0
    print(f"  Phase 2 done in {phase2_time:.1f}s")

    # ---- Sum up ----
    total = sum(multiplicity[bm] * aut_counts[bm] for bm in multiplicity)
    n_pairs = len(PERMS) ** 2
    E_aut = Fraction(total, n_pairs)

    print()
    print("=" * 70)
    print(f"  RESULT for N={N}:")
    print(f"    Sum |Aut| over (σ, τ) pairs: {total:,}")
    print(f"    n_pairs:                      {n_pairs:,}")
    print(f"    E[|Aut|]                    = {E_aut} "
          f"= {float(E_aut):.8f}")
    print(f"    unique 2-order shapes:        {n_unique:,}")
    A001035_at_7 = 6129859
    print(f"    A001035(7) = {A001035_at_7:,} labeled posets")
    print(f"    diff (dim>2 posets):          {A001035_at_7 - n_unique:,}")
    print(f"    total time: {time.time() - t0 + phase1_time:.1f}s "
          f"(P1: {phase1_time:.1f}s, P2: {phase2_time:.1f}s)")

    with open("result_N7.json", "w") as f:
        json.dump({
            "N": N,
            "sum_aut": total,
            "n_pairs": n_pairs,
            "E_aut_numerator": E_aut.numerator,
            "E_aut_denominator": E_aut.denominator,
            "n_unique_2orders": n_unique,
            "A001035_at_N": A001035_at_7,
            "n_dim3plus_posets": A001035_at_7 - n_unique,
            "phase1_time_sec": phase1_time,
            "phase2_time_sec": phase2_time,
        }, f, indent=2)
    print(f"  Saved to result_N7.json")


if __name__ == "__main__":
    main()
