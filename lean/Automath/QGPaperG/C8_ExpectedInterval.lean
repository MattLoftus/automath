/-
# C8: Expected interval size E[|{k : i ≺ k ≺ j}| | i ≺ j] = (N-2)/9

Calibration target #8 from QG Paper G (Loftus, exact-combinatorics, 2026), section
"Interval statistics" (Proposition: Expected interval size).

For a related pair `i ≺ j` in a random 2-order on `Fin N`, the expected number of
elements strictly between them — i.e., `k` with `i ≺ k ≺ j` — equals `(N-2)/9`.

We prove the **counting form**:
  36 · ∑_{(σ, τ)} totalIntervalCount σ τ = N(N-1)(N-2) · (N!)²,
which is equivalent to E[|interior| | i ≺ j] = (N-2)/9 after dividing by
the appropriate denominators.

## Proof

The argument generalises C1's pair-symmetry to triples:

1. **Triple-symmetry sub-lemma.** For three distinct positions `i, j, k` in `Fin N`:
   `6 · #{σ : σ i < σ k < σ j} = N!`.
   - The 3 classes "σ i max", "σ j max", "σ k max" partition `Perm (Fin N)`
     and have equal cardinality (via post-composition by transpositions on
     {i, j, k}). So each is `N!/3`.
   - Within "σ j max", the 2 sub-classes "σ i < σ k" and "σ k < σ i" partition
     and have equal cardinality (swap on i, k preserves "σ j max"). So each
     is `N!/6`.

2. **Fubini + factor.** The sum over (σ, τ, i, j, k) factors because i ≺ j ≺
   in σ and i ≺ k ≺ j in τ are independent.

3. **Distinct triple count.** N(N-1)(N-2) ordered distinct triples.

4. Combine.
-/
import Automath.QGPaperG.C1_OrderedPairCount

open Equiv Finset
open Automath.QGPaperG.C1

namespace Automath.QGPaperG.C8

variable {N : ℕ}

/-- Count of permutations with `σ i < σ k < σ j` for fixed indices. -/
def permLt3Count (i j k : Fin N) : ℕ :=
  (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ k ∧ σ k < σ j).card

/-- Count of permutations with `σ j` strictly larger than both `σ i` and `σ k`. -/
def permJMaxCount (i j k : Fin N) : ℕ :=
  (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j ∧ σ k < σ j).card

/-- 2-fold sub-symmetry: given `σ j` is max, `σ i < σ k` and `σ k < σ i` are
equally likely. So `2 · permLt3Count = permJMaxCount`. -/
lemma two_mul_permLt3Count (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    2 * permLt3Count i j k = permJMaxCount i j k := by
  classical
  unfold permLt3Count permJMaxCount
  -- Sj_left = {σ : σ i < σ k < σ j}, Sj_right = {σ : σ k < σ i < σ j} (within "σ j max")
  -- These are equal via σ ↦ σ ∘ (i ↔ k).
  have hcard :
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ k ∧ σ k < σ j).card =
      (Finset.univ.filter fun σ : Perm (Fin N) => σ k < σ i ∧ σ i < σ j).card := by
    apply Finset.card_bij'
      (fun σ _ => σ * Equiv.swap i k)
      (fun σ _ => σ * Equiv.swap i k)
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      refine ⟨?_, ?_⟩
      · -- (σ * swap i k) k < (σ * swap i k) i, i.e., σ i < σ k
        exact hσ.1
      · -- (σ * swap i k) i < (σ * swap i k) j, i.e., σ k < σ j
        rw [show Equiv.swap i k j = j from
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk]
        exact hσ.2
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      refine ⟨?_, ?_⟩
      · -- (σ * swap i k) i < (σ * swap i k) k, i.e., σ k < σ i
        exact hσ.1
      · -- (σ * swap i k) k < (σ * swap i k) j, i.e., σ i < σ j
        rw [show Equiv.swap i k j = j from
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk]
        exact hσ.2
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
  -- Disjoint: σ i < σ k and σ k < σ i can't both hold
  have hdisj :
      Disjoint (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ k ∧ σ k < σ j)
               (Finset.univ.filter fun σ : Perm (Fin N) => σ k < σ i ∧ σ i < σ j) := by
    rw [Finset.disjoint_filter]
    intros σ _ h1 h2
    exact (lt_asymm h1.1 h2.1).elim
  -- Union: σ ∈ Sj iff (σ i < σ k < σ j) or (σ k < σ i < σ j)
  -- (σ i and σ k are distinct values, so one of them is smaller. σ j is max ⇒ both < σ j.)
  have hunion :
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ k ∧ σ k < σ j) ∪
      (Finset.univ.filter fun σ : Perm (Fin N) => σ k < σ i ∧ σ i < σ j) =
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j ∧ σ k < σ j) := by
    ext σ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨lt_trans h1 h2, h2⟩
      · exact ⟨h2, lt_trans h1 h2⟩
    · rintro ⟨h1, h2⟩
      have h_ne : σ i ≠ σ k := fun heq => hik (σ.injective heq)
      rcases lt_or_gt_of_ne h_ne with hlt | hgt
      · exact Or.inl ⟨hlt, h2⟩
      · exact Or.inr ⟨hgt, h1⟩
  -- Combine: card_left + card_right = card_union, and card_left = card_right.
  have hsum :
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ k ∧ σ k < σ j).card +
      (Finset.univ.filter fun σ : Perm (Fin N) => σ k < σ i ∧ σ i < σ j).card =
      (Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j ∧ σ k < σ j).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  linarith

/-- 3-fold symmetry sub-lemma: Among `σ i, σ j, σ k`, exactly one is the max.
The three "max" classes have equal cardinality, so each is `N!/3`. -/
lemma three_mul_permJMaxCount (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    3 * permJMaxCount i j k = N.factorial := by
  classical
  unfold permJMaxCount
  -- The three classes
  set Si := Finset.univ.filter fun σ : Perm (Fin N) => σ j < σ i ∧ σ k < σ i with hSi
  set Sj := Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ j ∧ σ k < σ j with hSj
  set Sk := Finset.univ.filter fun σ : Perm (Fin N) => σ i < σ k ∧ σ j < σ k with hSk
  -- Si and Sj have equal cardinality via σ ↦ σ ∘ (i ↔ j).
  have hSi_Sj : Si.card = Sj.card := by
    apply Finset.card_bij'
      (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => σ * Equiv.swap i j)
    · intro σ hσ
      simp only [hSi, hSj, Finset.mem_filter, Finset.mem_univ, true_and,
                 Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      refine ⟨?_, ?_⟩
      · -- (σ * swap i j) i < (σ * swap i j) j, i.e., σ j < σ i
        exact hσ.1
      · -- (σ * swap i j) k < (σ * swap i j) j, i.e., σ k < σ i
        rw [show Equiv.swap i j k = k from
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
        exact hσ.2
    · intro σ hσ
      simp only [hSi, hSj, Finset.mem_filter, Finset.mem_univ, true_and,
                 Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      refine ⟨?_, ?_⟩
      · exact hσ.1
      · rw [show Equiv.swap i j k = k from
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
        exact hσ.2
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
  -- Sj and Sk have equal cardinality via σ ↦ σ ∘ (j ↔ k).
  have hSj_Sk : Sj.card = Sk.card := by
    apply Finset.card_bij'
      (fun σ _ => σ * Equiv.swap j k)
      (fun σ _ => σ * Equiv.swap j k)
    · intro σ hσ
      simp only [hSj, hSk, Finset.mem_filter, Finset.mem_univ, true_and,
                 Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      refine ⟨?_, ?_⟩
      · -- (σ * swap j k) i < (σ * swap j k) k, i.e., σ i < σ j
        rw [show Equiv.swap j k i = i from
            Equiv.swap_apply_of_ne_of_ne hij hik]
        exact hσ.1
      · -- (σ * swap j k) j < (σ * swap j k) k, i.e., σ k < σ j
        exact hσ.2
    · intro σ hσ
      simp only [hSj, hSk, Finset.mem_filter, Finset.mem_univ, true_and,
                 Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hσ ⊢
      refine ⟨?_, ?_⟩
      · rw [show Equiv.swap j k i = i from
            Equiv.swap_apply_of_ne_of_ne hij hik]
        exact hσ.1
      · exact hσ.2
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
    · intros σ _; simp [mul_assoc, Equiv.swap_mul_self]
  -- The three classes are pairwise disjoint and exhaust Perm(Fin N).
  have hdisj_Si_Sj : Disjoint Si Sj := by
    rw [Finset.disjoint_filter]
    intros σ _ h1 h2
    exact (lt_asymm h1.1 h2.1).elim
  have hdisj_Sj_Sk : Disjoint Sj Sk := by
    rw [Finset.disjoint_filter]
    intros σ _ h1 h2
    exact (lt_asymm h1.2 h2.2).elim
  have hdisj_Si_Sk : Disjoint Si Sk := by
    rw [Finset.disjoint_filter]
    intros σ _ h1 h2
    -- h1 : σ j < σ i ∧ σ k < σ i; h2 : σ i < σ k ∧ σ j < σ k
    -- contradiction: σ k < σ i and σ i < σ k
    exact (lt_asymm h1.2 h2.1).elim
  have hunion : Si ∪ Sj ∪ Sk = (Finset.univ : Finset (Perm (Fin N))) := by
    ext σ
    simp only [hSi, hSj, hSk, Finset.mem_union, Finset.mem_filter,
               Finset.mem_univ, true_and, iff_true]
    -- Among the three distinct values σ i, σ j, σ k, one is the maximum.
    have h_ij_ne : σ i ≠ σ j := fun heq => hij (σ.injective heq)
    have h_ik_ne : σ i ≠ σ k := fun heq => hik (σ.injective heq)
    have h_jk_ne : σ j ≠ σ k := fun heq => hjk (σ.injective heq)
    rcases lt_trichotomy (σ i) (σ j) with hij_lt | hij_eq | hij_gt
    · -- σ i < σ j
      rcases lt_trichotomy (σ j) (σ k) with hjk_lt | hjk_eq | hjk_gt
      · -- σ j < σ k, so σ k is max → in Sk
        right
        exact ⟨lt_trans hij_lt hjk_lt, hjk_lt⟩
      · exact absurd hjk_eq h_jk_ne
      · -- σ j > σ k, so σ j is max → in Sj
        left; right
        exact ⟨hij_lt, hjk_gt⟩
    · exact absurd hij_eq h_ij_ne
    · -- σ i > σ j
      rcases lt_trichotomy (σ i) (σ k) with hik_lt | hik_eq | hik_gt
      · -- σ i < σ k, so σ k is max → in Sk
        right
        exact ⟨hik_lt, lt_trans hij_gt hik_lt⟩
      · exact absurd hik_eq h_ik_ne
      · -- σ i > σ k, so σ i is max → in Si
        left; left
        exact ⟨hij_gt, hik_gt⟩
  -- Conclude.
  have hcard_sum : Si.card + Sj.card + Sk.card = (Finset.univ : Finset (Perm (Fin N))).card := by
    rw [← hunion]
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hdisj_Si_Sj]
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj_Si_Sk, hdisj_Sj_Sk⟩
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hcard_sum
  linarith [hSi_Sj, hSj_Sk]

/-- **Key sub-lemma:** `6 · permLt3Count i j k = N!` for distinct i, j, k. -/
lemma six_mul_permLt3Count (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    6 * permLt3Count i j k = N.factorial := by
  have h2 := two_mul_permLt3Count i j k hij hik hjk
  have h3 := three_mul_permJMaxCount i j k hij hik hjk
  -- 6 · permLt3Count = 3 · (2 · permLt3Count) = 3 · permJMaxCount = N!.
  linarith

/-- Sum-of-indicators reformulation of `permLt3Count`. -/
lemma sum_indicator_eq_permLt3Count (i j k : Fin N) :
    (∑ σ : Perm (Fin N), (if σ i < σ k ∧ σ k < σ j then (1 : ℕ) else 0)) =
    permLt3Count i j k := by
  classical
  unfold permLt3Count
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

/-- Total count of "interior" triples for a 2-order: ordered (i, j, k) with all distinct
positions and `i ≺ k ≺ j`. -/
def totalIntervalCount (σ τ : Perm (Fin N)) : ℕ :=
  ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
    (if i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        σ i < σ k ∧ σ k < σ j ∧ τ i < τ k ∧ τ k < τ j then 1 else 0)

/-- Indicator factorisation: the joint condition factors as the AND of distinctness
and the σ-chain and the τ-chain. -/
lemma ite_distinct_and_chain {p_dist p_σ p_τ : Prop}
    [Decidable p_dist] [Decidable p_σ] [Decidable p_τ] :
    (if p_dist ∧ p_σ ∧ p_τ then (1 : ℕ) else 0) =
    (if p_dist then 1 else 0) * (if p_σ then 1 else 0) * (if p_τ then 1 else 0) := by
  by_cases hd : p_dist
  · by_cases hs : p_σ
    · by_cases ht : p_τ
      · simp [hd, hs, ht]
      · simp [hd, hs, ht]
    · simp [hd, hs]
  · simp [hd]

/-- For any (i, j, k), the (σ, τ)-sum of the joint chain indicator factors as `permLt3Count²`.
(When (i, j, k) are not distinct, both sides are zero — no distinctness hypothesis needed.) -/
lemma sum_perm_pair_factor3 (i j k : Fin N) :
    (∑ p : Perm (Fin N) × Perm (Fin N),
      (if p.1 i < p.1 k ∧ p.1 k < p.1 j ∧ p.2 i < p.2 k ∧ p.2 k < p.2 j
       then (1 : ℕ) else 0)) =
    permLt3Count i j k * permLt3Count i j k := by
  classical
  rw [Fintype.sum_prod_type]
  -- Step A: regroup `A ∧ B ∧ C ∧ D` as `(A ∧ B) ∧ (C ∧ D)`, then use ite_and_eq_mul.
  have stepA :
      (∑ x : Perm (Fin N), ∑ y : Perm (Fin N),
        (if x i < x k ∧ x k < x j ∧ y i < y k ∧ y k < y j then (1 : ℕ) else 0)) =
      (∑ x : Perm (Fin N), ∑ y : Perm (Fin N),
        (if x i < x k ∧ x k < x j then (1 : ℕ) else 0) *
        (if y i < y k ∧ y k < y j then 1 else 0)) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have h_iff : (x i < x k ∧ x k < x j ∧ y i < y k ∧ y k < y j) ↔
                 ((x i < x k ∧ x k < x j) ∧ (y i < y k ∧ y k < y j)) := by tauto
    simp_rw [h_iff]
    exact ite_and_eq_mul
  rw [stepA]
  -- Step B: factor double sum into product of single sums.
  have stepB :
      (∑ x : Perm (Fin N), ∑ y : Perm (Fin N),
        (if x i < x k ∧ x k < x j then (1 : ℕ) else 0) *
        (if y i < y k ∧ y k < y j then 1 else 0)) =
      (∑ x : Perm (Fin N), if x i < x k ∧ x k < x j then (1 : ℕ) else 0) *
      (∑ y : Perm (Fin N), if y i < y k ∧ y k < y j then (1 : ℕ) else 0) :=
    (Fintype.sum_mul_sum (fun x : Perm (Fin N) => if x i < x k ∧ x k < x j then (1 : ℕ) else 0)
                         (fun y : Perm (Fin N) => if y i < y k ∧ y k < y j then (1 : ℕ) else 0)).symm
  rw [stepB, sum_indicator_eq_permLt3Count]

/-- For fixed distinct `i, j ∈ Fin N`, the count of `k ∈ Fin N` with `i ≠ k ∧ j ≠ k` is `N - 2`. -/
lemma card_complement_pair (i j : Fin N) (hij : i ≠ j) :
    ((Finset.univ : Finset (Fin N)).filter (fun k => i ≠ k ∧ j ≠ k)).card = N - 2 := by
  classical
  have heq : (Finset.univ : Finset (Fin N)).filter (fun k => i ≠ k ∧ j ≠ k)
           = ((Finset.univ : Finset (Fin N)).erase i).erase j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h2, Ne.symm h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h2, Ne.symm h1⟩
  rw [heq, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  · omega
  · rw [Finset.mem_erase]; exact ⟨hij.symm, Finset.mem_univ _⟩

/-- For each `i ∈ Fin N`, the count of `j ∈ Fin N` with `i ≠ j` is `N - 1`. -/
lemma card_complement_singleton (i : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun j => i ≠ j)).card = N - 1 := by
  classical
  have heq : (Finset.univ : Finset (Fin N)).filter (fun j => i ≠ j)
           = (Finset.univ : Finset (Fin N)).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩
  rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- Distinct ordered triple count: `#{(i, j, k) : Fin N × Fin N × Fin N | all distinct} = N(N-1)(N-2)`. -/
lemma card_distinct_triples :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0)) = N * (N - 1) * (N - 2) := by
  classical
  -- Inner k-sum: when (i, j) distinct, count k with i ≠ k ∧ j ≠ k = N - 2; otherwise 0.
  have h_k : ∀ i j : Fin N,
      (∑ k : Fin N, (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0))
      = (if i ≠ j then (N - 2 : ℕ) else 0) := by
    intros i j
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    by_cases hij : i ≠ j
    · rw [if_pos hij]
      have heq : (Finset.univ : Finset (Fin N)).filter (fun k => i ≠ j ∧ i ≠ k ∧ j ≠ k)
               = (Finset.univ : Finset (Fin N)).filter (fun k => i ≠ k ∧ j ≠ k) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩, fun ⟨h1, h2⟩ => ⟨hij, h1, h2⟩⟩
      rw [heq]
      exact card_complement_pair i j hij
    · rw [if_neg hij]
      have : (Finset.univ : Finset (Fin N)).filter (fun k => i ≠ j ∧ i ≠ k ∧ j ≠ k) = ∅ := by
        ext k; simp [hij]
      rw [this, Finset.card_empty]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_k i j))]
  -- Goal: ∑_i ∑_j (if i ≠ j then (N - 2) else 0) = N(N-1)(N-2).
  have h_j : ∀ i : Fin N,
      (∑ j : Fin N, (if i ≠ j then (N - 2 : ℕ) else 0))
      = (N - 1) * (N - 2) := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [card_complement_singleton i]
  rw [Finset.sum_congr rfl (fun i _ => h_j i)]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

/-- Multi-Fubini swap: a 4-deep nested `(σ, τ)` then triple-`(i, j, k)` sum
can be reordered to triple-`(i, j, k)` then `(σ, τ)`. -/
lemma fubini_swap (f : Perm (Fin N) × Perm (Fin N) → Fin N → Fin N → Fin N → ℕ) :
    (∑ p : Perm (Fin N) × Perm (Fin N), ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, f p i j k)
    = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ p : Perm (Fin N) × Perm (Fin N), f p i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- For each (i, j, k), the per-triple `(σ, τ)`-sum of the full indicator factors as
`⟦dist⟧ · permLt3Count²`. -/
lemma sum_perm_pair_full (i j k : Fin N) :
    (∑ p : Perm (Fin N) × Perm (Fin N),
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          p.1 i < p.1 k ∧ p.1 k < p.1 j ∧
          p.2 i < p.2 k ∧ p.2 k < p.2 j then (1 : ℕ) else 0))
    = (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0) * (permLt3Count i j k * permLt3Count i j k) := by
  classical
  by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
  · simp only [if_pos h, one_mul]
    -- When distinctness holds, the full indicator simplifies to just the chain conditions.
    have heq : (∑ p : Perm (Fin N) × Perm (Fin N),
                (if i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
                    p.1 i < p.1 k ∧ p.1 k < p.1 j ∧
                    p.2 i < p.2 k ∧ p.2 k < p.2 j then (1 : ℕ) else 0))
              = (∑ p : Perm (Fin N) × Perm (Fin N),
                (if p.1 i < p.1 k ∧ p.1 k < p.1 j ∧
                    p.2 i < p.2 k ∧ p.2 k < p.2 j then (1 : ℕ) else 0)) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [h]
    rw [heq]
    exact sum_perm_pair_factor3 i j k
  · simp only [if_neg h, zero_mul]
    apply Finset.sum_eq_zero
    intros p _
    have h_neg : ¬ (i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
                    p.1 i < p.1 k ∧ p.1 k < p.1 j ∧
                    p.2 i < p.2 k ∧ p.2 k < p.2 j) := by
      rintro ⟨h1, h2, h3, _⟩
      exact h ⟨h1, h2, h3⟩
    rw [if_neg h_neg]

/-- Per-triple identity: `36 · ⟦dist⟧ · permLt3Count² = ⟦dist⟧ · (N!)²`. -/
lemma triple_combined_identity (i j k : Fin N) :
    36 * ((if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0) *
          (permLt3Count i j k * permLt3Count i j k))
    = (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0) * (N.factorial)^2 := by
  by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
  · simp only [if_pos h, one_mul]
    have h6 : 6 * permLt3Count i j k = N.factorial :=
      six_mul_permLt3Count i j k h.1 h.2.1 h.2.2
    have : (6 * permLt3Count i j k) * (6 * permLt3Count i j k) = N.factorial * N.factorial := by
      rw [h6]
    nlinarith [this]
  · simp only [if_neg h, zero_mul, mul_zero]

/-- **Main theorem: C8 (counting form).**
For all `N`,
  `36 · ∑_{(σ, τ)} totalIntervalCount σ τ = N(N-1)(N-2) · (N!)²`,
equivalently `E[|interior| | i ≺ j] = (N-2)/9`. -/
theorem EIntervalSize_counting (N : ℕ) :
    36 * ∑ p : Perm (Fin N) × Perm (Fin N), totalIntervalCount p.1 p.2
    = N * (N - 1) * (N - 2) * (N.factorial)^2 := by
  classical
  unfold totalIntervalCount
  -- Step 1: multi-Fubini to swap (σ, τ) sum past (i, j, k) sums.
  rw [fubini_swap]
  -- Step 2: For each (i, j, k), apply sum_perm_pair_full.
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => sum_perm_pair_full i j k)))]
  -- Goal: 36 * ∑_i ∑_j ∑_k (⟦dist⟧ · permLt3Count²) = N(N-1)(N-2) · (N!)²
  -- Step 3: distribute 36 inside, apply triple_combined_identity.
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => by rw [Finset.mul_sum]))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => Finset.sum_congr rfl (fun k _ => triple_combined_identity i j k)))]
  -- Goal: ∑_i ∑_j ∑_k (⟦dist⟧ · (N!)²) = N(N-1)(N-2) · (N!)²
  -- Step 4: factor (N!)² out and apply card_distinct_triples.
  have hfactor : ∀ i j : Fin N,
      (∑ k : Fin N, ((if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0) * (N.factorial)^2))
      = (∑ k : Fin N, (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0)) * (N.factorial)^2 := by
    intros i j
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hfactor i j))]
  have hfactor2 : ∀ i : Fin N,
      (∑ j : Fin N, (∑ k : Fin N, (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0)) * (N.factorial)^2)
      = (∑ j : Fin N, ∑ k : Fin N, (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0)) * (N.factorial)^2 := by
    intro i; rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun i _ => hfactor2 i)]
  rw [← Finset.sum_mul, card_distinct_triples]

end Automath.QGPaperG.C8
