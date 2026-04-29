# exp06 — Round E — E[|Aut|] at N=6, N=7 (two new exact values)

**Date:** 2026-04-29 (Session 6, Round E)
**Outcome:** ✅ Two new exact values computed via direct enumeration. Lean formalization partial (N=2..5 via `native_decide`, N=6 and N=7 stated as `axiom` due to kernel-time limits).

## Result

For uniformly random 2-orders on `Fin N` from `(σ, τ) ∈ Sym(N) × Sym(N)`:

```
E[|Aut|] at N=6  =  349/80    =  4.3625    (NEW)
E[|Aut|] at N=7  =  3479/720  =  4.83194…  (NEW)
```

Sequence:

| N | E[\|Aut\|] | decimal | ∑ \|Aut\| | unique 2-order shapes | dim-3+ posets |
|---|----------|---------|-----------|------------------------|---------------|
| 2 | 3/2      | 1.5000  | 6         | 3                      | 0             |
| 3 | 13/6     | 2.1667  | 78        | 19                     | 0             |
| 4 | 71/24    | 2.9583  | 1,704     | 219                    | 0             |
| 5 | 89/24    | 3.7083  | 53,400    | 4,231                  | 0             |
| **6** | **349/80** | **4.3625** | **2,261,520** | **129,183**       | **840**       |
| **7** | **3479/720** | **4.8319** | **122,739,120** | **5,844,259**     | **285,600**   |

N=2..5 match Loftus's QG Paper G hand calculations exactly. N=6 and N=7 are the new exact values — this is the **Round E open-problem extension result**.

## External validation

The "unique 2-order shapes" column matches OEIS A001035 (number of partial orders on `n` labeled points) for N=2..5: 3, 19, 219, 4231 ✓.

At N=6, A001035 = **130,023** but our 2-order count is **129,183**. The difference of **840** is exactly the number of labeled posets on 6 elements that have **dimension > 2** — i.e., posets that are NOT realizable as the intersection of two total orders.

At N=7, A001035 = **6,129,859** and our 2-order count is **5,844,259**. The difference of **285,600** is the dim-3+ count at N=7 (labeled).

This is a known phenomenon: the first dim-3 posets appear at N=6 (Trotter, *Combinatorics and Partially Ordered Sets*, Theorem 8.3.4 and related). Our enumeration provides independent confirmation **and** computes the exact dim-3+ counts at N=6, 7 from first principles. These dim-3+ counts (840 and 285,600) may themselves be a contribution worth submitting to OEIS.

## Algorithm

Brute-force enumeration with caching by 2-order shape.

**N=6** (script `compute_e_aut.py`):
1. Compute the partial order as a `frozenset` of `(i, j)` pairs with `i ≺ j`.
2. Cache the automorphism count keyed by the 2-order shape. The 518,400 pairs collapse to 129,183 distinct shapes (a 4× reduction).
3. For each unique shape, count automorphisms by iterating `π ∈ Sym(N)` and checking `(π i, π j) ∈ order` for every `(i, j) ∈ order`. (Since `π` is a bijection, forward containment implies the image equals `order`, so no separate "preserves non-precedence" check is needed.)
4. Compute time: **21.6 seconds**, single-threaded, on Matt's M4 Pro.

**N=7** (script `compute_n7_full.py`):
1. Same algorithm but with **bitmask encoding** of 2-orders as 49-bit integers (much faster than `frozenset`).
2. Phase 1 (enumerate 25.4M pairs, build multiplicity dict): **82s single-threaded**.
3. Phase 2 (count automorphisms per unique shape): **multiprocessing across 14 workers**, ~469s.
4. Total: **~9.2 minutes**, parallelized.

Single-thread N=7 estimate was ~7 hours; multiprocessing brought it to ~9 min.

## Lean formalization

The Lean file `Automath/QGPaperG/RoundE_AutN6.lean` defines:

```lean
def numAuts {N : ℕ} (σ τ : Perm (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Perm (Fin N))).filter
    (fun π => decide (∀ i j : Fin N,
      ((σ i < σ j ∧ τ i < τ j) ↔ (σ (π i) < σ (π j) ∧ τ (π i) < τ (π j)))))).card

def autSum (N : ℕ) : ℕ :=
  ∑ p : Perm (Fin N) × Perm (Fin N), numAuts p.1 p.2
```

And asserts:

| Theorem | Proof | Build time |
|---------|-------|------------|
| `autSum_two : autSum 2 = 6` | `native_decide` | <1s |
| `autSum_three : autSum 3 = 78` | `native_decide` | ~5s |
| `autSum_four : autSum 4 = 1704` | `native_decide` | ~10s |
| `autSum_five : autSum 5 = 53400` | `native_decide` | ~94s (full file rebuild) |
| `autSum_six : autSum 6 = 2261520` | `axiom` | `native_decide` killed at ~10 min CPU |
| `autSum_seven : autSum 7 = 122739120` | `axiom` | not attempted (would require ~6·10¹² Lean kernel ops; orders of magnitude beyond N=6) |

The N=6 case scales as 518,400 × 720 × 36 ≈ 1.3·10¹⁰ operations through Lean's `Equiv.Perm (Fin 6)` machinery — the `Equiv` indirection is heavy. Killed after ~10 minutes of single-core compute. To make the kernel-checked proof feasible would require either:

(a) Replacing `Equiv.Perm` with an unwrapped `Vector (Fin N) N` representation that `native_decide` can compute on as raw arrays (refactor work, not just one-liner).
(b) A structural proof avoiding brute-force enumeration. No clean path identified — the value 349/80 doesn't have an obvious closed-form pattern matching the N=2..5 sequence (denominators 2, 6, 24, 24, 80 don't follow `N!`).

For now, `autSum_six` is stated as `axiom`. The methods paper will discuss this honestly: **the new mathematical content (the value 349/80) is established by reproducible external enumeration; Lean's role is the precise statement and the rest of the calibration framework.** This is consistent with computer-assisted proofs in combinatorics (e.g., the Four Color Theorem's original Appel-Haken computation was external; the formal Lean/Coq verification came later via different methods).

## Significance for the project

Per PLAYBOOK §12 scoring rubric:
- Calibration-only: 7.0–7.5 ceiling.
- **Calibration + new mathematical result: 8.0–8.5 ceiling.**

The new exact value 349/80 is a publishable contribution to extremal combinatorics on its own (target venue: J. Combin. Theory A or Random Structures & Algorithms). Combined with the methods paper, this gives the **8.0–8.5 trajectory** the project was aiming at.

Two papers expected:
1. **Methods paper** at JAR / ITP: Claude Code + Lean pipeline, calibrated on QG Paper G (5/10 theorems).
2. **Combinatorics paper** at J. Combin. Theory A: extension of E[|Aut|] for random 2-orders to N=6, with the dimension-3 poset count (A001035 - 2-orders) as a side result.

## Files

- `compute_e_aut.py` — Python enumeration script (132 lines).
- `lean/Automath/QGPaperG/RoundE_AutN6.lean` — Lean formalization.
- `notes.md` — this file.

## Sequence analysis with N=2..7 in hand

**∑|Aut|/N!:** 3, 13, 71, 445, 3141, 24353

**Ratios (a_{N+1}/a_N):** 4.333, 5.462, 6.268, 7.058, 7.753

The ratios grow roughly linearly with N (slope ~0.7–0.8), but no clean recurrence emerges from a 3-term linear-recurrence-with-constants fit (least-squares gives non-integer coefficients 13.5, -40.7, 16.1 — looks like noise).

**Differences in E[|Aut|]:** 0.667, 0.792, 0.750, 0.654, 0.469.

The differences peak at N=3→4 and then decline. **Suggestive that E[|Aut|] grows sublinearly** as N → ∞, but with only 6 data points and the high computational cost of additional values, we cannot rule out other behaviors.

**No OEIS match** for either 6, 78, 1704, 53400, 2261520, 122739120 or 3, 13, 71, 445, 3141, 24353. These appear to be new sequences worth submitting to OEIS as part of the combinatorics paper.

**Per RESEARCH_LEARNINGS lesson 97** ("characterize an exact result is a 6.0–6.5 strategy"), without a closed-form formula or recurrence, the standalone result remains in the "characterization extension" class. Combined with the methods paper, the joint contribution is honestly **7.0–7.5 score**, not 8.0–8.5 as the PLAYBOOK had estimated.

## Next steps

- Submit two new sequences to OEIS:
  - The dim-3+ labeled-poset count: 0, 0, 0, 0, 840, 285600 (for N=2..7).
  - The ∑|Aut| sequence: 6, 78, 1704, 53400, 2261520, 122739120.
  - And/or E[|Aut|] sequence as numerator/denominator pairs.
- Begin methods paper draft incorporating the 5/10 calibration + Round E result.
- Consider computing N=8 if a focused effort can reveal a recurrence — but this would be ~100+ hours of compute (or a smarter algorithm via nauty/canonical labeling). Probably not worth it without a leading hypothesis.
