/-
# C4 (case k=2): E[# 2-element antichains] = N(N−1)/4

Calibration target #4 from QG Paper G (Loftus, exact-combinatorics, 2026), restricted
to the k=2 case. The general claim is E[# k-element antichains] = C(N, k)/k! for any k;
proving the general k case requires partitioning over k-subsets of `Fin N` and showing
each contributes 1/k! to the expectation. The k=2 case is a clean corollary of C2 and
serves as the calibration anchor.

We prove the **ordered** counting form:
  2 · ∑_{(σ, τ)} numOrderedIncomparablePairs σ τ = N(N-1) · (N!)².

The unordered antichain count follows by dividing the ordered count by 2 — at
each (σ, τ), the ordered incomparable count is exactly twice the unordered
2-antichain count, because incomparability is symmetric and `i ≠ j` is enforced
via `offDiag`. Hence the unordered counting form is
  4 · ∑_{(σ, τ)} numTwoAntichains σ τ = N(N-1) · (N!)²,
which gives `E[#2-antichains] = N(N-1)/4 = C(N, 2)/2!`, matching the QG paper.

## Proof
At any (σ, τ): every ordered pair `(i, j)` with `i ≠ j` is EITHER comparable
(`i ≺ j ∨ j ≺ i`) OR incomparable (neither direction). The two are exclusive
and exhaustive. So
  numOrderedIncomparablePairs σ τ + comparablePairCount σ τ = N(N-1).
Summing over (σ, τ) and applying C2 (`2·∑ comparablePairCount = N(N-1)·(N!)²`)
yields the result.
-/
import Automath.QGPaperG.C2_OrderingFraction

open Equiv Finset
open Automath.QGPaperG.C1
open Automath.QGPaperG.C2

namespace Automath.QGPaperG.C4

variable {N : ℕ}

/-- Count of ordered pairs `(i, j)` with `i ≠ j` that are incomparable in the
2-order from `(σ, τ)` — i.e., NOT `i ≺ j` AND NOT `j ≺ i`. -/
def numOrderedIncomparablePairs (σ τ : Perm (Fin N)) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
    (if ¬((σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1))
     then 1 else 0)

/-- Indicator decomposition: ⟦¬P⟧ = 1 - ⟦P⟧ for ℕ-valued indicators when ⟦P⟧ ∈ {0,1}.
Stated as `⟦¬P⟧ + ⟦P⟧ = 1`. -/
lemma ite_not_add_ite {p : Prop} [Decidable p] :
    (if ¬p then (1 : ℕ) else 0) + (if p then 1 else 0) = 1 := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]

/-- For each off-diagonal pair, the indicator-pair sum is 1 (every pair is
either comparable or incomparable, exclusively). -/
lemma incomparable_plus_comparable_indicator (σ τ : Perm (Fin N)) (p : Fin N × Fin N) :
    (if ¬((σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1))
     then (1 : ℕ) else 0) +
    (if (σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1)
     then 1 else 0) = 1 :=
  ite_not_add_ite

/-- Pointwise sum: `numOrderedIncomparablePairs + comparablePairCount = #offDiag = N(N-1)`. -/
lemma incomparable_plus_comparable_eq (σ τ : Perm (Fin N)) :
    numOrderedIncomparablePairs σ τ + comparablePairCount σ τ = N * (N - 1) := by
  unfold numOrderedIncomparablePairs comparablePairCount
  rw [← Finset.sum_add_distrib]
  have h_pointwise : ∀ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      ((if ¬((σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1))
        then (1 : ℕ) else 0) +
       (if (σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1)
        then 1 else 0)) = 1 :=
    fun p _ => incomparable_plus_comparable_indicator σ τ p
  rw [Finset.sum_congr rfl h_pointwise]
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  exact card_offDiag_fin

/-- **Main theorem: C4 at k=2 (ordered counting form).**
For all `N`,
  `2 · ∑_{(σ, τ)} numOrderedIncomparablePairs σ τ = N(N−1) · (N!)²`,
equivalent to `E[# 2-antichains] = N(N−1)/4 = C(N, 2)/2!` after dividing by 2 to
go from ordered to unordered antichains. -/
theorem ETwoAntichains_counting (N : ℕ) :
    2 * ∑ p : Perm (Fin N) × Perm (Fin N), numOrderedIncomparablePairs p.1 p.2
    = N * (N - 1) * (N.factorial)^2 := by
  -- Step 1: ∑_{(σ,τ)} (inc + comp) = N(N-1) · (N!)².
  have h_pointwise : ∀ p ∈ (Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))),
      numOrderedIncomparablePairs p.1 p.2 + comparablePairCount p.1 p.2 = N * (N - 1) :=
    fun p _ => incomparable_plus_comparable_eq p.1 p.2
  have h_sum_combined :
      (∑ p : Perm (Fin N) × Perm (Fin N),
        (numOrderedIncomparablePairs p.1 p.2 + comparablePairCount p.1 p.2))
      = (N.factorial)^2 * (N * (N - 1)) := by
    rw [Finset.sum_congr rfl h_pointwise]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ,
        Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
    ring
  rw [Finset.sum_add_distrib] at h_sum_combined
  -- Step 2: Apply C2.
  have hC2 : 2 * ∑ p : Perm (Fin N) × Perm (Fin N), comparablePairCount p.1 p.2
           = N * (N - 1) * (N.factorial)^2 := EOrderingFraction_counting N
  -- Step 3: linear-arith conclusion. Treat ∑ inc and ∑ comp as opaque.
  set Sinc := ∑ p : Perm (Fin N) × Perm (Fin N), numOrderedIncomparablePairs p.1 p.2 with hSi
  set Scomp := ∑ p : Perm (Fin N) × Perm (Fin N), comparablePairCount p.1 p.2 with hSc
  set K := N * (N - 1) * (N.factorial)^2 with hK
  have hK_alt : K = (N.factorial)^2 * (N * (N - 1)) := by rw [hK]; ring
  -- h_sum_combined: Sinc + Scomp = K (after rewriting via hK_alt)
  -- hC2: 2 * Scomp = K
  -- Goal: 2 * Sinc = K
  rw [← hK_alt] at h_sum_combined
  linarith

end Automath.QGPaperG.C4
