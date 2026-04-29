#!/usr/bin/env python3
"""
Compute E[|Aut|] for random 2-orders on Fin N, for N = 2..6.

A 2-order from (sigma, tau) in Sym(N) x Sym(N) is the partial order
on {0, 1, ..., N-1} where i prec j iff sigma[i] < sigma[j] AND tau[i] < tau[j].

An automorphism of the 2-order is a permutation pi in Sym(N) such that
i prec j iff pi[i] prec pi[j] for all i, j.

E[|Aut|] = (sum over (sigma, tau) of |Aut|) / (N!)^2.

We verify against QG Paper G's hand-computed values for N=2..5:
  N=2: 3/2
  N=3: 13/6
  N=4: 71/24
  N=5: 89/24
and report the exact rational value for N=6.

Brute force over all (sigma, tau) pairs and all candidate pi's. With caching
of "order signature" (frozenset of prec-pairs) the inner loop is dominated
by automorphism counting per unique order shape.
"""
from itertools import permutations
from fractions import Fraction
import time
import sys

def two_order(sigma, tau):
    """Return the 2-order (set of (i, j) with i prec j) as a frozenset."""
    N = len(sigma)
    return frozenset(
        (i, j) for i in range(N) for j in range(N)
        if i != j and sigma[i] < sigma[j] and tau[i] < tau[j]
    )


def count_auts_given_order(order, N, all_perms):
    """Count permutations pi such that pi preserves the partial order
    given by `order` (a frozenset of (i, j) prec-pairs).

    Since pi is a bijection on Fin N, the map (i, j) -> (pi[i], pi[j])
    is also a bijection on offDiag(Fin N). If (pi[i], pi[j]) is in `order`
    for every (i, j) in `order`, then |image| = |order| and image is a subset
    of order, so image = order. So just checking forward containment suffices."""
    count = 0
    for pi in all_perms:
        if all((pi[i], pi[j]) in order for (i, j) in order):
            count += 1
    return count


def compute_E_aut(N):
    """Compute E[|Aut|] for random 2-orders on Fin N as an exact Fraction."""
    perms = list(permutations(range(N)))
    n_pairs = len(perms) ** 2

    # Cache: order signature -> automorphism count
    cache = {}
    total_aut = 0
    n_orders_processed = 0

    t0 = time.time()
    for idx, sigma in enumerate(perms):
        for tau in perms:
            order = two_order(sigma, tau)
            if order not in cache:
                cache[order] = count_auts_given_order(order, N, perms)
            total_aut += cache[order]
            n_orders_processed += 1

        if N >= 5:
            elapsed = time.time() - t0
            done = (idx + 1) / len(perms)
            est_total = elapsed / max(done, 1e-9)
            sys.stdout.write(
                f"\r  N={N}: sigma {idx+1}/{len(perms)} "
                f"({done*100:.1f}%), unique orders cached: {len(cache)}, "
                f"elapsed {elapsed:.1f}s / est total {est_total:.1f}s"
            )
            sys.stdout.flush()

    if N >= 5:
        print()  # newline after progress bar

    return Fraction(total_aut, n_pairs), len(cache), total_aut


def main():
    expected = {
        2: Fraction(3, 2),
        3: Fraction(13, 6),
        4: Fraction(71, 24),
        5: Fraction(89, 24),
    }

    print("Computing E[|Aut|] for random 2-orders on Fin N")
    print("=" * 70)

    for N in [2, 3, 4, 5, 6]:
        t0 = time.time()
        E_aut, n_unique_orders, total_aut = compute_E_aut(N)
        dt = time.time() - t0
        n_pairs = (1 if N == 0 else
                   {2: 4, 3: 36, 4: 576, 5: 14400, 6: 518400}[N])
        print(f"\nN={N}:")
        print(f"  total |Aut| summed:    {total_aut:,}")
        print(f"  total (sigma, tau) pairs: {n_pairs:,}")
        print(f"  unique 2-order shapes: {n_unique_orders:,}")
        print(f"  E[|Aut|]               = {E_aut} "
              f"= {float(E_aut):.6f}")
        if N in expected:
            match = E_aut == expected[N]
            print(f"  expected (QG paper):    {expected[N]} "
                  f"= {float(expected[N]):.6f}  "
                  f"{'MATCH' if match else 'MISMATCH'}")
            if not match:
                print(f"  ERROR: computed value does not match QG paper!")
                sys.exit(1)
        print(f"  computed in {dt:.2f}s")
        print("-" * 70)

    print("\nAll values verified against QG Paper G hand calculations.")
    print("N=6 is the new computed result (Round E).")


if __name__ == "__main__":
    main()
