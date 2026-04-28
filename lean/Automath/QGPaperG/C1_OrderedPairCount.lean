/-
# C1: Expected number of ordered comparable pairs in a random 2-order

Calibration target #1 from QG Paper G (Loftus, exact-combinatorics, 2026).

A 2-order on `Fin N` is a pair of permutations `(σ, τ) : Perm (Fin N) × Perm (Fin N)`.
For elements `i j : Fin N` we say `i ≺ j` iff `σ i < σ j` and `τ i < τ j`.

We prove the **counting identity**:
  4 · ∑_{(σ,τ)} (# ordered pairs (i, j) with i ≺ j) = N(N-1) · (N!)²,
which is equivalent (under uniform distribution) to
  E[# ordered comparable pairs] = N(N-1)/4.

## Proof outline
1. **Fubini swap.** ∑_{(σ,τ)} ∑_{(i,j) | i≠j} ⟦σ i < σ j ∧ τ i < τ j⟧
                  = ∑_{(i,j) | i≠j} ∑_{(σ,τ)} ⟦σ i < σ j⟧ · ⟦τ i < τ j⟧.
2. **Independence (product factor).** ∑_{(σ,τ)} ⟦P σ⟧·⟦Q τ⟧
                  = (∑_σ ⟦P σ⟧) · (∑_τ ⟦Q τ⟧).
3. **Swap-symmetry lemma.** For fixed `i ≠ j`, the involution σ ↦ σ ∘ Equiv.swap i j
   pairs each σ having σ i < σ j with one having σ i > σ j. Together they exhaust
   Sym(N), so #{σ : σ i < σ j} · 2 = N!.
4. **Combine.** Each (i, j) contributes (N!/2)² = (N!)²/4. There are N(N-1) such
   ordered pairs, so the total is N(N-1) · (N!)² / 4.
-/
import Mathlib

open Equiv Finset

namespace Automath.QGPaperG.C1

variable {N : ℕ}

/-- Number of permutations of `Fin N` placing `σ i` strictly below `σ j`. -/
def permLtCount (i j : Fin N) : ℕ :=
  (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j).card

/-- Half the permutations of `Fin N` send `i` strictly below `j` (when `i ≠ j`).
Stated as `2 · count = N!` to avoid `ℕ` division. -/
lemma two_mul_permLtCount (i j : Fin N) (hij : i ≠ j) :
    2 * permLtCount i j = N.factorial := by
  classical
  unfold permLtCount
  -- Bijection σ ↦ σ * (swap i j) between {σ : σ i < σ j} and {σ : σ j < σ i}.
  have hcard :
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j).card =
      (Finset.univ.filter fun σ : Perm (Fin N) => σ j < σ i).card := by
    apply Finset.card_bij'
      (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => σ * Equiv.swap i j)
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      exact hσ
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
  -- Disjoint and exhaustive partition of `Perm (Fin N)`.
  have hdisj :
      Disjoint (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j)
               (Finset.univ.filter fun σ : Perm (Fin N) => σ j < σ i) := by
    rw [Finset.disjoint_filter]; intros _ _ hlt hgt; exact (lt_asymm hlt hgt).elim
  have hunion :
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j) ∪
      (Finset.univ.filter fun σ : Perm (Fin N) => σ j < σ i) =
      (Finset.univ : Finset (Perm (Fin N))) := by
    ext σ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases lt_trichotomy (σ i) (σ j) with h | h | h
    · exact Or.inl h
    · exact absurd (σ.injective h) hij
    · exact Or.inr h
  have hpart :
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j).card +
      (Finset.univ.filter fun σ : Perm (Fin N) => σ j < σ i).card = N.factorial := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
        Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  linarith

/-- Off-diagonal pairs in `Fin N` count exactly `N(N-1)`. -/
lemma card_offDiag_fin :
    ((Finset.univ : Finset (Fin N)).offDiag).card = N * (N - 1) := by
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  cases N with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel]
    have h : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
    omega

/-- Ordered comparable pair count for a 2-order `(σ, τ)`. -/
def orderedPairCount (σ τ : Perm (Fin N)) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
    (if σ p.1 < σ p.2 ∧ τ p.1 < τ p.2 then 1 else 0)

/-- Indicator factorisation: `⟦P σ ∧ Q τ⟧ = ⟦P σ⟧ · ⟦Q τ⟧` for ℕ-valued indicators. -/
lemma ite_and_eq_mul {p q : Prop} [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℕ) else 0) = (if p then 1 else 0) * (if q then 1 else 0) := by
  by_cases hp : p
  · by_cases hq : q
    · simp [hp, hq]
    · simp [hp, hq]
  · simp [hp]

/-- `∑_σ ⟦σ i < σ j⟧ = permLtCount i j` (in ℕ). -/
lemma sum_indicator_eq_permLtCount (i j : Fin N) :
    (∑ σ : Perm (Fin N), (if σ i < σ j then (1 : ℕ) else 0)) = permLtCount i j := by
  classical
  unfold permLtCount
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

/-- For each off-diagonal pair `(i, j)`, the sum over `(σ, τ)` of the joint indicator
factors as `permLtCount i j * permLtCount i j`. -/
lemma sum_perm_pair_factor (i j : Fin N) :
    (∑ p : Perm (Fin N) × Perm (Fin N),
      (if p.1 i < p.1 j ∧ p.2 i < p.2 j then (1 : ℕ) else 0)) =
    permLtCount i j * permLtCount i j := by
  classical
  rw [Fintype.sum_prod_type]
  -- Step A: turn the joint indicator into a product of marginals.
  have stepA :
      (∑ x : Perm (Fin N), ∑ y : Perm (Fin N),
        (if x i < x j ∧ y i < y j then (1 : ℕ) else 0)) =
      (∑ x : Perm (Fin N), ∑ y : Perm (Fin N),
        (if x i < x j then (1 : ℕ) else 0) * (if y i < y j then 1 else 0)) :=
    Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => ite_and_eq_mul
  rw [stepA]
  -- Step B: factor the double sum into a product of single sums (with explicit f, g).
  have stepB :
      (∑ x : Perm (Fin N), ∑ y : Perm (Fin N),
        (if x i < x j then (1 : ℕ) else 0) * (if y i < y j then 1 else 0)) =
      (∑ x : Perm (Fin N), if x i < x j then (1 : ℕ) else 0) *
      (∑ y : Perm (Fin N), if y i < y j then (1 : ℕ) else 0) :=
    (Fintype.sum_mul_sum (fun x : Perm (Fin N) => if x i < x j then (1 : ℕ) else 0)
                         (fun y : Perm (Fin N) => if y i < y j then (1 : ℕ) else 0)).symm
  rw [stepB, sum_indicator_eq_permLtCount]

/-- **Main theorem: C1 (counting form).**
For all `N`,
  `4 · ∑_{(σ, τ)} orderedPairCount σ τ = N · (N-1) · (N!)²`,
equivalently `E[orderedPairCount] = N(N-1)/4` under the uniform distribution
on `Perm (Fin N) × Perm (Fin N)` (cardinality `(N!)²`). -/
theorem ELinkCount_counting (N : ℕ) :
    4 * ∑ p : Perm (Fin N) × Perm (Fin N), orderedPairCount p.1 p.2
    = N * (N - 1) * (N.factorial)^2 := by
  classical
  -- Step 1: open `orderedPairCount`, swap the (σ,τ)-sum and the (i,j)-sum, factor.
  have step1 :
      ∑ p : Perm (Fin N) × Perm (Fin N), orderedPairCount p.1 p.2
      = ∑ ij ∈ (Finset.univ : Finset (Fin N)).offDiag,
          permLtCount ij.1 ij.2 * permLtCount ij.1 ij.2 := by
    simp only [orderedPairCount]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ij _ => ?_
    exact sum_perm_pair_factor ij.1 ij.2
  rw [step1]
  -- Step 2: each off-diagonal (i, j) contributes (N!/2)² = (N!)²/4 via swap symmetry.
  have step2 : ∀ ij ∈ (Finset.univ : Finset (Fin N)).offDiag,
      4 * (permLtCount ij.1 ij.2 * permLtCount ij.1 ij.2) = (N.factorial)^2 := by
    intro ij hij
    rw [Finset.mem_offDiag] at hij
    have hne : ij.1 ≠ ij.2 := hij.2.2
    have h := two_mul_permLtCount ij.1 ij.2 hne
    -- (2 * count)² = N!² ⟹ 4 * count² = N!²
    have : (2 * permLtCount ij.1 ij.2)^2 = N.factorial^2 := by rw [h]
    linarith [sq_nonneg (permLtCount ij.1 ij.2), this, sq (permLtCount ij.1 ij.2),
              sq (2 * permLtCount ij.1 ij.2), mul_pow 2 (permLtCount ij.1 ij.2) 2]
  -- Step 3: distribute the 4 across the sum and apply step2 to every term.
  rw [show (4 * ∑ ij ∈ (Finset.univ : Finset (Fin N)).offDiag,
              permLtCount ij.1 ij.2 * permLtCount ij.1 ij.2) =
            ∑ ij ∈ (Finset.univ : Finset (Fin N)).offDiag,
              4 * (permLtCount ij.1 ij.2 * permLtCount ij.1 ij.2) from by
        rw [Finset.mul_sum]]
  rw [Finset.sum_congr rfl step2]
  rw [Finset.sum_const, smul_eq_mul, card_offDiag_fin]

end Automath.QGPaperG.C1
