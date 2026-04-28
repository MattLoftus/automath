/-
# C2: Expected ordering fraction E[f] = 1/2

Calibration target #2 from QG Paper G (Loftus, exact-combinatorics, 2026).

The **ordering fraction** of a 2-order `(σ, τ)` is
  f(σ, τ) := R(σ, τ) / [N(N-1)],
where R(σ, τ) is the count of ordered pairs `(i, j) ∈ Fin N × Fin N` with
`i ≠ j` such that either `i ≺ j` or `j ≺ i`. The QG paper's claim is
  E[f] = 1/2  (uniform distribution on Perm × Perm).

We prove the **counting identity**:
  2 · ∑_{(σ, τ)} comparablePairCount σ τ = N(N-1) · (N!)²,
which is equivalent to E[f] = 1/2 because dividing by N(N-1)·(N!)² gives 1/2.

## Proof
Observation: `comparablePairCount = 2 · orderedPairCount` (where
`orderedPairCount` is C1's strict-precedence count). This holds because the
disjunction "i ≺ j ∨ j ≺ i" decomposes as a disjoint union — these two
events are mutually exclusive at any (i, j) since `<` is irreflexive — and
the second sum reindexes to the first via the swap `(i, j) ↔ (j, i)` on
`offDiag`. Then C2 follows directly from C1 (ELinkCount_counting):
  2 · ∑ comparablePairCount = 2 · ∑ (2 · orderedPairCount)
                            = 4 · ∑ orderedPairCount = N(N-1) · (N!)².
-/
import Automath.QGPaperG.C1_OrderedPairCount

open Equiv Finset
open Automath.QGPaperG.C1

namespace Automath.QGPaperG.C2

variable {N : ℕ}

/-- Disjoint disjunction: ⟦P ∨ Q⟧ = ⟦P⟧ + ⟦Q⟧ in ℕ when `P ∧ Q` is impossible. -/
lemma ite_or_disjoint_eq_add {p q : Prop} [Decidable p] [Decidable q] (h : ¬(p ∧ q)) :
    (if p ∨ q then (1 : ℕ) else 0) = (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p
  · by_cases hq : q
    · exact absurd ⟨hp, hq⟩ h
    · simp [hp, hq]
  · simp [hp]

/-- Comparable ordered pair count for a 2-order `(σ, τ)`: number of ordered
pairs `(i, j) : Fin N × Fin N` with `i ≠ j` such that `i ≺ j` or `j ≺ i`. -/
def comparablePairCount (σ τ : Perm (Fin N)) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
    (if (σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1) then 1 else 0)

/-- Disjointness: at any pair, both `i ≺ j` and `j ≺ i` cannot hold. -/
lemma compr_disjoint (σ τ : Perm (Fin N)) (p : Fin N × Fin N) :
    ¬((σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∧ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1)) := by
  rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
  exact absurd (lt_trans h1 h2) (lt_irrefl _)

/-- Reindex offDiag-sum via swap `(p.1, p.2) ↔ (p.2, p.1)`. The "j ≺ i at p"
indicator equals the "i ≺ j at swap(p)" indicator, so the two sums are equal. -/
lemma sum_swap_offDiag (σ τ : Perm (Fin N)) :
    (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      (if σ p.2 < σ p.1 ∧ τ p.2 < τ p.1 then (1 : ℕ) else 0)) =
    (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
      (if σ p.1 < σ p.2 ∧ τ p.1 < τ p.2 then (1 : ℕ) else 0)) := by
  -- Helper: offDiag is closed under Prod.swap.
  have offDiag_swap_mem : ∀ p : Fin N × Fin N,
      p ∈ (Finset.univ : Finset (Fin N)).offDiag →
      Prod.swap p ∈ (Finset.univ : Finset (Fin N)).offDiag := by
    intro p hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩
  refine Finset.sum_nbij' Prod.swap Prod.swap
    offDiag_swap_mem offDiag_swap_mem
    (fun p _ => Prod.swap_swap p) (fun p _ => Prod.swap_swap p)
    (fun p _ => ?_)
  -- Value match: at p, indicator on (p.2, p.1) → at swap(p), indicator on (p.1, p.2).
  rfl

/-- **Bridge to C1: comparablePairCount = 2 · orderedPairCount.** -/
lemma comparablePairCount_eq_two_orderedPairCount (σ τ : Perm (Fin N)) :
    comparablePairCount σ τ = 2 * orderedPairCount σ τ := by
  unfold comparablePairCount
  -- Split the disjunction's indicator into the sum of two indicators.
  have step1 :
      (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        (if (σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1) then (1 : ℕ) else 0)) =
      (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        ((if σ p.1 < σ p.2 ∧ τ p.1 < τ p.2 then (1 : ℕ) else 0) +
         (if σ p.2 < σ p.1 ∧ τ p.2 < τ p.1 then 1 else 0))) :=
    Finset.sum_congr rfl fun p _ => ite_or_disjoint_eq_add (compr_disjoint σ τ p)
  rw [step1, Finset.sum_add_distrib, sum_swap_offDiag]
  unfold orderedPairCount
  ring

/-- **Main theorem: C2 (counting form).**
For all `N`,
  `2 · ∑_{(σ, τ)} comparablePairCount σ τ = N(N-1) · (N!)²`,
equivalently `E[f] = 1/2` under the uniform distribution on `Perm × Perm`. -/
theorem EOrderingFraction_counting (N : ℕ) :
    2 * ∑ p : Perm (Fin N) × Perm (Fin N), comparablePairCount p.1 p.2
    = N * (N - 1) * (N.factorial)^2 := by
  have h : ∀ p : Perm (Fin N) × Perm (Fin N),
      comparablePairCount p.1 p.2 = 2 * orderedPairCount p.1 p.2 :=
    fun p => comparablePairCount_eq_two_orderedPairCount p.1 p.2
  simp_rw [h]
  rw [← Finset.mul_sum]
  rw [show 2 * (2 * ∑ p : Perm (Fin N) × Perm (Fin N), orderedPairCount p.1 p.2) =
            4 * ∑ p : Perm (Fin N) × Perm (Fin N), orderedPairCount p.1 p.2 from by ring]
  exact ELinkCount_counting N

end Automath.QGPaperG.C2
