/-
# Round E: E[|Aut|] = 349/80 for random 2-orders on Fin 6

A new exact value extending QG Paper G's automorphism-group computation. Matt Loftus
hand-computed the values for N = 2, 3, 4, 5: 3/2, 13/6, 71/24, 89/24. This file
asserts the N = 6 value `E[|Aut|] = 349/80` (equivalently, ∑ |Aut| = 2,261,520
over the 518,400 (σ, τ) pairs in `Sym(6) × Sym(6)`).

## Computation

The value was computed by direct enumeration in Python (see
`experiments/exp06_e_aut/compute_e_aut.py`). The script enumerates all
`(σ, τ) ∈ Sym(N)^2`, builds the resulting 2-order as a frozenset of `(i, j)`
with `i ≺ j`, caches by 2-order shape, and counts automorphisms `π ∈ Sym(N)`
preserving the order. Verification against Loftus's hand calculations:

  N | E[|Aut|] | unique 2-orders | OEIS A001035 (labeled posets)
  --|----------|-----------------|------------------------------
  2 | 3/2      | 3               | 3 (matches; all posets are 2-orders)
  3 | 13/6     | 19              | 19 (matches)
  4 | 71/24    | 219             | 219 (matches)
  5 | 89/24    | 4,231           | 4,231 (matches)
  6 | 349/80   | 129,183         | 130,023 (840 dim-3 posets are NOT 2-orders)

The cross-check against OEIS A001035 (and the known fact that the first
dimension-3 posets appear at N=6) provides independent external validation.

## Lean status

`native_decide` is too slow for N = 6 — the theorem requires enumerating
518,400 (σ, τ) pairs × 720 candidate π's × 36 pair-condition checks ≈ 13
billion operations through Lean's encoded `Equiv.Perm (Fin 6)` machinery.
Killed at ~10 min of single-core compute. The cleaner alternative would be:
(a) decode `Perm (Fin 6)` as a flat array of `Fin 720 → Fin 6 → Fin 6` to
let `native_decide` use raw computation, or (b) prove via a structural
combinatorial argument (currently no clean path identified).

For Round E, we therefore commit:
- `autSum_two`, `autSum_three`, `autSum_four`, `autSum_five` all proved by
  `native_decide` (kernel-verified). N=5 takes ~94s in the full file rebuild
  but does converge.
- `autSum_six` STATED and asserted as `axiom` with the Python-verified value,
  with full reproducibility code in `experiments/exp06_e_aut/compute_e_aut.py`.

The methods paper will discuss the computational vs. kernel-checked verification
trade-off honestly. The mathematical content (the new exact value 349/80 for
N = 6) is established by enumeration; Lean's role is the precise statement
and the calibration framework, not the brute-force compute.

This is the ROUND E open-problem extension result. Together with the methods
paper covering the calibration set (C1, C2, C4@k=2, C5, C8), this gives the
combinatorics-paper material for a standalone J. Combin. Theory A or
Random Structures & Algorithms submission.
-/
import Mathlib

namespace Automath.QGPaperG.RoundE

open Equiv Finset

/-- For a 2-order from `(σ, τ) : Perm (Fin N)²`, the count of permutations
`π ∈ Perm (Fin N)` that preserve the order. -/
def numAuts {N : ℕ} (σ τ : Perm (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Perm (Fin N))).filter
    (fun π => decide (∀ i j : Fin N,
      ((σ i < σ j ∧ τ i < τ j) ↔ (σ (π i) < σ (π j) ∧ τ (π i) < τ (π j)))))).card

/-- Sum of |Aut| over all `(σ, τ)` pairs in `Sym(N)²`. Equal to `(N!)² · E[|Aut|]`. -/
def autSum (N : ℕ) : ℕ :=
  ∑ p : Perm (Fin N) × Perm (Fin N), numAuts p.1 p.2

/-- **N = 2 — known value 3/2 → integer counting form: ∑ |Aut| = 6.** -/
theorem autSum_two : autSum 2 = 6 := by
  native_decide

/-- **N = 3 — known value 13/6 → integer counting form: ∑ |Aut| = 78.** -/
theorem autSum_three : autSum 3 = 78 := by
  native_decide

/-- **N = 4 — known value 71/24 → integer counting form: ∑ |Aut| = 1704.** -/
theorem autSum_four : autSum 4 = 1704 := by
  native_decide

/-- **N = 5 — known value 89/24 → integer counting form: ∑ |Aut| = 53,400.** -/
theorem autSum_five : autSum 5 = 53400 := by
  native_decide

/-- **Round E result (N = 6): ∑ |Aut| at N = 6 equals 2,261,520, equivalent to E[|Aut|] = 349/80.**

This extends QG Paper G's hand calculations:
  N=2: 3/2,  N=3: 13/6,  N=4: 71/24,  N=5: 89/24  →  **N=6: 349/80** (new).

The value `2261520` was verified by direct enumeration in Python (see
`experiments/exp06_e_aut/compute_e_aut.py`), with full reproducibility:
the script also re-derives N=2..5 values matching `autSum_two`..`autSum_five`,
and Loftus's hand-computed values from QG Paper G.

`native_decide` was attempted but is too slow at N=6 due to the 518,400 × 720 × 36
≈ 1.3·10¹⁰ pair-condition checks through `Equiv.Perm (Fin 6)`. Stated as `axiom`
pending either: (a) an efficient native encoding via `Fin 720 → Fin 6 → Fin 6`
arrays, or (b) a structural proof. -/
axiom autSum_six : autSum 6 = 2261520

/-- **Round E result (N = 7): ∑ |Aut| at N = 7 equals 122,739,120, equivalent to E[|Aut|] = 3479/720.**

The full sequence for N=2..7:
  N=2: 3/2,  N=3: 13/6,  N=4: 71/24,  N=5: 89/24,  N=6: 349/80,  **N=7: 3479/720** (new).

Verified by parallelized enumeration in Python (`experiments/exp06_e_aut/compute_n7_full.py`).
~9.2 minutes total: ~82s for Phase 1 (enumerating 25.4M pairs into 5.84M unique 2-order shapes),
then ~469s for Phase 2 (counting automorphisms with 14 worker processes).

External cross-check: the unique-2-order count (5,844,259) plus the dimension-3+ poset count
(285,600) sums to 6,129,859 = OEIS A001035(7) = number of labeled posets on 7 elements.

Stated as `axiom` (not even `native_decide`-attempted; would require 25.4M × 5040 × 49 ≈
6·10¹² operations — orders of magnitude beyond the N=6 timeout). -/
axiom autSum_seven : autSum 7 = 122739120

end Automath.QGPaperG.RoundE
