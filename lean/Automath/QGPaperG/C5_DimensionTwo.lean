/-
# C5: P(poset dim = 2) = 1 − 1/N! for random 2-orders

Calibration target #5 from QG Paper G (Loftus, exact-combinatorics, 2026).

A 2-order on `Fin N` from `(σ, τ) : Perm (Fin N) × Perm (Fin N)` has dim ≤ 2
by construction. The QG paper shows dim ≤ 1 (i.e., the 2-order is itself a
total order) iff `σ = τ`. Therefore:
  P(dim = 2) = P(σ ≠ τ) = 1 − P(σ = τ) = 1 − N! / (N!)² = 1 − 1/N!.

We prove the **counting form**:
  #{(σ, τ) : σ ≠ τ} + N! = (N!)²,
which immediately yields P(dim = 2) = 1 − 1/N! once divided by `(N!)²`.

## Two bridging lemmas (used / deferred)

* **EASY (used here):** `σ = τ → is2OrderTotallyOrdered σ τ` — included as
  `diag_is_total_order` below.
* **HARD (deferred):** `is2OrderTotallyOrdered σ τ → σ = τ` — i.e., a 2-order
  that's a total order forces `σ = τ`. This requires "any strictly monotone
  permutation of `Fin N` is the identity," which is true but not currently a
  one-line Mathlib lookup. We document this bridge in the project but defer
  the formal Lean proof to a follow-up. The counting result below is rigorous
  on its own; the bridge is what connects "σ = τ" to the QG paper's "dim ≤ 1".

## Proof of the counting form
The identity `Perm × Perm = (diagonal) ⊔ (off-diagonal)` is a disjoint union.
The diagonal `{(σ, σ) : σ ∈ Perm}` is the image of `(univ : Finset Perm)` under
the injection `σ ↦ (σ, σ)`, hence has cardinality `N!` by `Fintype.card_perm`.
The total cardinality is `|Perm × Perm| = (N!)²`. Therefore the off-diagonal
count is `(N!)² - N!`, and adding `N!` gives `(N!)²`.
-/
import Mathlib
import Automath.QGPaperG.C1_OrderedPairCount

open Equiv Finset

namespace Automath.QGPaperG.C5

variable {N : ℕ}

/-- Diagonal predicate: the 2-order is a total order. -/
def is2OrderTotallyOrdered (σ τ : Perm (Fin N)) : Prop :=
  ∀ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
    (σ p.1 < σ p.2 ∧ τ p.1 < τ p.2) ∨ (σ p.2 < σ p.1 ∧ τ p.2 < τ p.1)

/-- **Bridge (easy direction):** if `σ = τ`, the 2-order is a total order. -/
lemma diag_is_total_order (σ τ : Perm (Fin N)) (h : σ = τ) :
    is2OrderTotallyOrdered σ τ := by
  intro p hp
  rw [Finset.mem_offDiag] at hp
  have hne : p.1 ≠ p.2 := hp.2.2
  -- σ injective ⇒ σ p.1 ≠ σ p.2 ⇒ exactly one direction holds.
  have : σ p.1 ≠ σ p.2 := fun heq => hne (σ.injective heq)
  rcases lt_or_gt_of_ne this with hlt | hgt
  · left; exact ⟨hlt, by rw [← h]; exact hlt⟩
  · right; exact ⟨hgt, by rw [← h]; exact hgt⟩

/-- The diagonal of `Perm × Perm` has cardinality `N!`. -/
lemma card_diagonal_perm :
    ((Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).filter
      (fun p => p.1 = p.2)).card = N.factorial := by
  classical
  have heq : (Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).filter (fun p => p.1 = p.2)
           = (Finset.univ : Finset (Perm (Fin N))).image (fun σ => (σ, σ)) := by
    ext ⟨σ, τ⟩
    constructor
    · intro hστ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hστ
      refine Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, ?_⟩
      simp [hστ]
    · rintro himg
      obtain ⟨ρ, _, hρ⟩ := Finset.mem_image.mp himg
      simp only [Prod.mk.injEq] at hρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hρ.1, hρ.2]
  rw [heq, Finset.card_image_of_injective _ (fun σ τ h => (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- Off-diagonal and diagonal partition `Perm × Perm`. -/
lemma card_offDiagonal_add_diagonal :
    ((Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).filter
      (fun p => p.1 ≠ p.2)).card +
    ((Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).filter
      (fun p => p.1 = p.2)).card =
    (Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).card := by
  classical
  rw [add_comm, Finset.card_filter_add_card_filter_not]

/-- **Main theorem: C5 (counting form).**
For all `N`,
  `#{(σ, τ) : σ ≠ τ} + N! = (N!)²`,
equivalently `P(σ ≠ τ) = 1 − 1/N!`. By the QG-paper bridge `is2OrderTotallyOrdered ⇔ σ = τ`,
this matches `P(poset dim = 2) = 1 − 1/N!`. -/
theorem PdimTwo_counting (N : ℕ) :
    ((Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).filter
      (fun p => p.1 ≠ p.2)).card + N.factorial = (N.factorial)^2 := by
  have h1 := card_offDiagonal_add_diagonal (N := N)
  rw [card_diagonal_perm] at h1
  rw [h1, Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  ring

end Automath.QGPaperG.C5
