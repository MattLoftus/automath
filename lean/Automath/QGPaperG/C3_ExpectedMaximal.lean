/-
# C3: Expected number of maximal elements E[# maximal] = H_N

Calibration target #3 from QG Paper G (Loftus, exact-combinatorics, 2026), Section
"Extremal elements" (Theorem: Expected number of maximal elements).

For a uniformly random 2-order on `Fin N` from `(σ, τ) ∈ Perm (Fin N) × Perm (Fin N)`,
the expected number of *maximal* elements equals the N-th harmonic number
`H_N = 1 + 1/2 + 1/3 + ... + 1/N`.

We prove the **counting form**:
  ∑_{(σ, τ)} numMaximal(σ, τ) = ∑_{k=1}^{N} (N!)²/k,
where each summand `(N!)²/k` is an integer (since `k ∣ N!` for `k ≤ N`). Dividing by
`(N!)²` gives `E[# maximal] = ∑_{k=1}^{N} 1/k = H_N`.

## Proof outline

The key reduction is the **right-to-left max bijection**: for `π := τ ∘ σ⁻¹ ∈ Perm (Fin N)`,
the element `σ⁻¹(a) ∈ Fin N` is maximal in the 2-order from `(σ, τ)` iff `π(a)` is the
maximum value of `π` restricted to `{a, a+1, ..., N-1}`. Concretely:

* `σ⁻¹(a)` is maximal iff for every element `j = σ⁻¹(b)` with `b > a`,
  it is NOT the case that `σ(σ⁻¹(a)) < σ(σ⁻¹(b))` AND `τ(σ⁻¹(a)) < τ(σ⁻¹(b))`.
* The σ-condition `a < b` always holds (since `b > a`), so the requirement reduces to
  `τ(σ⁻¹(a)) ≥ τ(σ⁻¹(b))` for every `b > a`, i.e., `π(a) ≥ π(b)` for every `b > a`.
* This is precisely the definition of "right-to-left max at position `a` in `π`".

Hence `numMaximal(σ, τ) = numRTLMax(π)` where `π = τ ∘ σ⁻¹`.

The bijection `(σ, τ) ↔ (σ, π)` (with `π := τ ∘ σ⁻¹`) is a bijection on
`Perm (Fin N) × Perm (Fin N)`, so:

  ∑_{(σ, τ)} numMaximal(σ, τ) = ∑_{σ} ∑_{π} numRTLMax(π) = N! · ∑_π numRTLMax(π).

Then `∑_π numRTLMax(π) = ∑_{a ∈ Fin N} #{π : π(a) is max of π[a..N-1]}`. For each
position `a`, the count is `N!/(N - a.val)` by `(N - a.val)`-fold symmetry: among
the `N - a.val` positions `{a, a+1, ..., N-1}`, each is equally likely to host the
max value. Multiplying by `N - a.val`: `(N - a.val) · count = N!`.

So `∑_π numRTLMax(π) = ∑_a N!/(N - a.val) = ∑_{k=1}^{N} N!/k`, giving
`∑ numMaximal = N! · ∑_k N!/k = ∑_k (N!)²/k`.

The counting form sidesteps Mathlib's harmonic-number `ℚ` machinery: we state the
sum directly in `ℕ` using exact division (`ℕ.div`) since each `(N!)² / k` is integer.

## Status (Session 8, 2026-04-29)

Drafting in progress. The core sub-lemmas are:

1. `numMaximal_eq_numRTLMax`: the right-to-left max bijection.
2. `bijection_sum`: ∑ over `(σ, τ)` reduces to N! · ∑ over π.
3. `card_perm_a_max_suffix`: for each position `a ∈ Fin N`,
   `(N - a.val) · count = N!`.
4. Main theorem: combine the above.
-/
import Mathlib
import Automath.QGPaperG.C1_OrderedPairCount

open Equiv Finset

namespace Automath.QGPaperG.C3

variable {N : ℕ}

/-- Element `i ∈ Fin N` is **maximal** in the 2-order from `(σ, τ)` if no `j ≠ i`
satisfies `σ i < σ j ∧ τ i < τ j`. -/
def isMaximal (σ τ : Perm (Fin N)) (i : Fin N) : Prop :=
  ∀ j : Fin N, j ≠ i → ¬ (σ i < σ j ∧ τ i < τ j)

instance (σ τ : Perm (Fin N)) (i : Fin N) : Decidable (isMaximal σ τ i) := by
  unfold isMaximal
  exact inferInstance

/-- Number of maximal elements in the 2-order from `(σ, τ)`. -/
def numMaximal (σ τ : Perm (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (isMaximal σ τ)).card

/-- A position `a ∈ Fin N` is a **right-to-left maximum** of `π` if `π a ≥ π b`
for every `b ≥ a`. (Equivalently, `π a = max π[a..N-1]` since `π` is injective.) -/
def isRTLMax (π : Perm (Fin N)) (a : Fin N) : Prop :=
  ∀ b : Fin N, a.val ≤ b.val → π b ≤ π a

instance (π : Perm (Fin N)) (a : Fin N) : Decidable (isRTLMax π a) := by
  unfold isRTLMax
  exact inferInstance

/-- Number of right-to-left maxima of a permutation `π`. -/
def numRTLMax (π : Perm (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (isRTLMax π)).card

/-- **Bridge: numMaximal(σ, τ) = numRTLMax(τ ∘ σ⁻¹).**
For each element `i = σ⁻¹(a)` indexed by its σ-rank `a`, `i` is maximal in the
2-order iff `a` is a right-to-left max of `π := τ ∘ σ⁻¹`. -/
lemma numMaximal_eq_numRTLMax (σ τ : Perm (Fin N)) :
    numMaximal σ τ = numRTLMax (τ * σ⁻¹) := by
  classical
  unfold numMaximal numRTLMax
  -- Bijection: i ↦ σ i, restricted to Fin N. The map σ : Fin N → Fin N is a bijection.
  apply Finset.card_bij' (fun i _ => σ i) (fun a _ => σ⁻¹ a)
  · -- forward maps in: if i is maximal then σ i is RTLMax of π
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro b hb
    -- Need: π b ≤ π (σ i), where π = τ * σ⁻¹.
    -- Equivalently: τ (σ⁻¹ b) ≤ τ (σ⁻¹ (σ i)) = τ i.
    show (τ * σ⁻¹) b ≤ (τ * σ⁻¹) (σ i)
    simp only [Equiv.Perm.mul_apply]
    show τ (σ⁻¹ b) ≤ τ (σ⁻¹ (σ i))
    rw [show σ⁻¹ (σ i) = i from σ.symm_apply_apply i]
    -- Goal: τ (σ⁻¹ b) ≤ τ i
    -- We have hi : ∀ j ≠ i, ¬ (σ i < σ j ∧ τ i < τ j).
    -- We have hb : (σ i).val ≤ b.val.
    -- Set j = σ⁻¹ b. Either j = i, in which case τ (σ⁻¹ b) = τ i and ≤ holds.
    -- Or j ≠ i. Apply hi to j: ¬ (σ i < σ j ∧ τ i < τ j) i.e., σ i ≥ σ j ∨ τ i ≥ τ j.
    -- σ j = σ (σ⁻¹ b) = b (using σ.apply_symm_apply).
    -- σ i = σ i. From hb, σ i ≤ b. Combined with σ i ≠ b (since j ≠ i ⇒ σ i ≠ σ j = b):
    -- σ i < b. So σ i < σ j is true. So we must have τ i ≥ τ j, i.e., τ i ≥ τ (σ⁻¹ b).
    by_cases hji : σ⁻¹ b = i
    · rw [hji]
    · -- σ⁻¹ b ≠ i.
      have h_sigma_neq : σ i ≠ b := by
        intro heq
        apply hji
        rw [show b = σ i from heq.symm]
        exact σ.symm_apply_apply i
      have h_sigma_lt : σ i < b := lt_of_le_of_ne hb h_sigma_neq
      have h_dont_dominate := hi (σ⁻¹ b) hji
      -- h_dont_dominate : ¬ (σ i < σ (σ⁻¹ b) ∧ τ i < τ (σ⁻¹ b))
      have h_sigma_apply : σ (σ⁻¹ b) = b := by
        show σ (σ.symm b) = b
        exact σ.apply_symm_apply b
      rw [h_sigma_apply] at h_dont_dominate
      -- h_dont_dominate : ¬ (σ i < b ∧ τ i < τ (σ⁻¹ b))
      -- Conclude τ i ≥ τ (σ⁻¹ b) using h_sigma_lt.
      by_contra h_lt
      exact h_dont_dominate ⟨h_sigma_lt, lt_of_not_ge h_lt⟩
  · -- backward maps in: if a is RTLMax of π then σ⁻¹ a is maximal
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    intro j hji
    -- Need: ¬ (σ (σ⁻¹ a) < σ j ∧ τ (σ⁻¹ a) < τ j).
    -- σ (σ⁻¹ a) = a. So need: ¬ (a < σ j ∧ τ (σ⁻¹ a) < τ j).
    rintro ⟨h_sigma_lt, h_tau_lt⟩
    have h_sigma_a : σ (σ⁻¹ a) = a := by
      show σ (σ.symm a) = a
      exact σ.apply_symm_apply a
    rw [h_sigma_a] at h_sigma_lt
    -- h_sigma_lt : a < σ j
    -- Apply ha to b = σ j (so a.val ≤ (σ j).val).
    have h_le : a.val ≤ (σ j).val := le_of_lt h_sigma_lt
    have := ha (σ j) h_le
    -- this : (τ * σ⁻¹) (σ j) ≤ (τ * σ⁻¹) a
    simp only [Equiv.Perm.mul_apply] at this
    have h_inv_apply : σ⁻¹ (σ j) = j := by
      show σ.symm (σ j) = j
      exact σ.symm_apply_apply j
    rw [h_inv_apply] at this
    -- this : τ j ≤ τ (σ⁻¹ a)
    exact absurd h_tau_lt (not_lt.mpr this)
  · intro i _
    exact σ.symm_apply_apply i
  · intro a _
    exact σ.apply_symm_apply a

/-- The bijection `(σ, τ) ↔ (σ, τ ∘ σ⁻¹)` on `Perm (Fin N) × Perm (Fin N)`
allows the sum over `(σ, τ)` to be rewritten as `N!` times the sum over `π`. -/
lemma bijection_sum (f : Perm (Fin N) → ℕ) :
    ∑ p : Perm (Fin N) × Perm (Fin N), f (p.2 * p.1⁻¹) =
    Fintype.card (Perm (Fin N)) * ∑ π : Perm (Fin N), f π := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun σ _ => ?_)]
  · rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  · -- For fixed σ, ∑_τ f (τ * σ⁻¹) = ∑_π f π via π := τ * σ⁻¹.
    apply Finset.sum_bij' (fun τ _ => τ * σ⁻¹) (fun π _ => π * σ)
    · intros; exact Finset.mem_univ _
    · intros; exact Finset.mem_univ _
    · intros τ _; group
    · intros π _; group
    · intros τ _; rfl

/-- For each fixed position `a ∈ Fin N`, the count of permutations `π` with
`π a` being the maximum of `π[a..N-1]` equals `N!/(N - a.val)`. Stated as
`(N - a.val) · count = N!` to avoid `ℕ` division.

This is the analog of C1's `two_mul_permLtCount`, generalized to `(N - a.val)`-fold
symmetry over positions `{a, a+1, ..., N-1}`.

**Proof strategy (deferred):** Partition `Perm (Fin N)` into classes `M_b` for
`b ∈ [a, N)` where `M_b := {π : π b is max of π[a..N-1]}`. Each `M_b` has equal
cardinality to `M_a` via post-composition by `Equiv.swap a b`. Combining:
`(N - a.val) · |M_a| = |Perm (Fin N)| = N!`.

The full Lean proof requires (i) cardinality of the suffix `{b : a.val ≤ b.val}`
equal to `N - a.val`, (ii) bijection between `M_a` and `M_b` via `Equiv.swap`, and
(iii) the partition argument. Each piece is comparable in complexity to C8's 6-fold
symmetry proof but parameterized by `(N - a.val)`. Estimated ~150 lines to complete.
Currently `sorry`'d, similar to Round E's N=6 axiom situation. -/
lemma card_perm_rtl_max_at_pos (a : Fin N) :
    (N - a.val) * (Finset.univ.filter
      (fun π : Perm (Fin N) => isRTLMax π a)).card = N.factorial := by
  sorry

/-- Sum of right-to-left max counts over all permutations. -/
lemma sum_numRTLMax :
    ∑ π : Perm (Fin N), numRTLMax π
    = ∑ a : Fin N, (Finset.univ.filter (fun π : Perm (Fin N) => isRTLMax π a)).card := by
  classical
  unfold numRTLMax
  -- ∑_π #{a : isRTLMax π a} = ∑_π ∑_a ⟦isRTLMax π a⟧ = ∑_a ∑_π ⟦isRTLMax π a⟧ = ∑_a #{π : isRTLMax π a}
  have h_per_pi : ∀ π : Perm (Fin N),
      ((Finset.univ : Finset (Fin N)).filter (isRTLMax π)).card =
      ∑ a : Fin N, (if isRTLMax π a then (1 : ℕ) else 0) := by
    intro π
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun π _ => h_per_pi π)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]

/-- **Main theorem: C3 (counting form).**
For all `N ≥ 1`,
  `∑_{(σ, τ)} numMaximal(σ, τ) · ∏_{k=1}^{N} k = ∑_{k=1}^{N} (N!)² · ∏_{j ≠ k} j`,
i.e., `∑ numMaximal = (N!)² · H_N` after dividing by `(N!)²`.

Stated in pure-ℕ counting form using `(N!)²/k` (each summand integer since `k ≤ N`). -/
theorem ENumMaximal_counting (N : ℕ) :
    ∑ p : Perm (Fin N) × Perm (Fin N), numMaximal p.1 p.2
    = ∑ a : Fin N, (N.factorial)^2 / (N - a.val) := by
  classical
  -- Step 1: substitute numMaximal(σ, τ) = numRTLMax(τ * σ⁻¹).
  have step1 : ∀ p : Perm (Fin N) × Perm (Fin N),
      numMaximal p.1 p.2 = numRTLMax (p.2 * p.1⁻¹) :=
    fun p => numMaximal_eq_numRTLMax p.1 p.2
  rw [Finset.sum_congr rfl (fun p _ => step1 p)]
  -- Step 2: bijection_sum reduces ∑_{(σ,τ)} f(τ * σ⁻¹) to N! · ∑_π f(π).
  rw [bijection_sum]
  rw [Fintype.card_perm, Fintype.card_fin]
  -- Step 3: ∑_π numRTLMax = ∑_a #{π : isRTLMax π a}.
  rw [sum_numRTLMax]
  -- Step 4: each per-position count multiplied by (N - a.val) equals N!.
  -- Hence the per-position count is N!/(N - a.val) (integer since N - a.val ≤ N and divides).
  -- Total: ∑_a (N!)²/(N - a.val) (after multiplying by N! once).
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Goal: N! * #{π : isRTLMax π a} = N!² / (N - a.val)
  have h := card_perm_rtl_max_at_pos a
  -- h : (N - a.val) * #count = N!
  -- So #count = N! / (N - a.val) (exact since N - a.val divides N! for a < N).
  -- Then N! * #count = N! * (N! / (N - a.val)) = N!² / (N - a.val).
  have h_pos : 0 < N - a.val := by
    have ha : a.val < N := a.isLt
    omega
  have h_div : (N - a.val) ∣ N.factorial := by
    -- (N - a.val) ≤ N, and any k ≤ N divides N.factorial.
    have : N - a.val ≤ N := Nat.sub_le _ _
    exact Nat.dvd_factorial h_pos this
  rw [pow_two]
  rw [Nat.mul_div_assoc _ h_div]
  rw [show N.factorial = (N - a.val) * (Finset.univ.filter
        (fun π : Perm (Fin N) => isRTLMax π a)).card from h.symm]
  rw [Nat.mul_div_cancel_left _ h_pos]

end Automath.QGPaperG.C3
