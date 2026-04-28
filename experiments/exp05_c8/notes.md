# exp05 — C8 — Expected interval size E[|interior| | i ≺ j] = (N−2)/9

**Date:** 2026-04-28 (Session 4, Round C continuation)
**Outcome:** ⚠ **Partial.** Sub-lemmas all compile; main theorem and `card_distinct_triples` deferred to Session 5.
**Lines:** 338

## What's proven (the genuine new mathematical content)

The triple-symmetry generalisation of C1's pair-symmetry:

```
lemma six_mul_permLt3Count (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    6 * permLt3Count i j k = N.factorial
```

Where `permLt3Count i j k = #{σ : σ i < σ k < σ j}`. Proved via the standard combinatorial decomposition:

1. **3-fold symmetry** (`three_mul_permJMaxCount`): which of `σ i, σ j, σ k` is the maximum splits `Perm(Fin N)` into 3 disjoint exhaustive classes (Si, Sj, Sk). Equal cardinality via post-composition by transpositions on `{i, j, k}`. So each is `N!/3`.
2. **2-fold sub-symmetry** (`two_mul_permLt3Count`): within "σ j is max", the two sub-classes "σ i < σ k" and "σ k < σ i" are equally large via `σ ↦ σ ∘ (i ↔ k)`. So each is `N!/6`.
3. Combine: `6 · permLt3Count = 3 · (2 · permLt3Count) = 3 · permJMaxCount = N!`.

The bijection-based 3-fold symmetry is **the genuine generalization** of C1's `two_mul_permLtCount`. Same proof pattern (Equiv.swap on group, partition + equal cardinality), now over a 3-element rather than 2-element index set.

## Also proven

- `sum_perm_pair_factor3 (i j k : Fin N)` — the joint (σ, τ)-sum of the chain indicator factors as `permLt3Count(i,j,k)²`. Distinctness hypothesis NOT needed — when (i, j, k) are not distinct, both sides are 0.
- `ite_distinct_and_chain` — the indicator decomposition `⟦dist ∧ σ-chain ∧ τ-chain⟧ = ⟦dist⟧ · ⟦σ-chain⟧ · ⟦τ-chain⟧`.
- `sum_indicator_eq_permLt3Count` — `∑_σ ⟦σ i < σ k < σ j⟧ = permLt3Count`.

## What's deferred (the Fubini orchestration)

Two `sorry`s remain:

```
lemma card_distinct_triples :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℕ) else 0)) = N * (N - 1) * (N - 2)

theorem EIntervalSize_counting (N : ℕ) :
    36 * ∑ p : Perm (Fin N) × Perm (Fin N), totalIntervalCount p.1 p.2
    = N * (N - 1) * (N - 2) * (N.factorial)^2
```

**Mathematical content:** none new. `card_distinct_triples` is "N choices for i, then N-1 for j, then N-2 for k." Main theorem is Fubini + the sub-lemmas.

**Why deferred:** the Lean orchestration hits HO-unification issues with `rw [show ∀ i j, f i j = g i j from ...]` patterns. Specifically:

1. Nested `Finset.sum_filter` rewrites to compute `card_distinct_triples` get tangled in `Finset.sum_comm` and erase-card identities.
2. The main theorem requires pulling the (σ, τ) sum past 3 nested (i, j, k) sums — Mathlib has `Finset.sum_comm` for adjacent swaps but the multi-swap requires careful sequencing.
3. Each rewrite needs to interact correctly with `if`-condition Decidable instances.

The fixes are mechanical (probably 30 more minutes in a focused session) but I hit my Session 4 budget.

## Per-step verification rate

| # | Lemma | First-try |
|---|-------|-----------|
| 1 | `permLt3Count` (def) | ✅ |
| 2 | `permJMaxCount` (def) | ✅ |
| 3 | `two_mul_permLt3Count` | ❌ → ✅ (1 fix) |
| 4 | `three_mul_permJMaxCount` | ❌ → ✅ (1 fix) |
| 5 | `six_mul_permLt3Count` | ✅ |
| 6 | `sum_indicator_eq_permLt3Count` | ✅ |
| 7 | `totalIntervalCount` (def) | ✅ |
| 8 | `ite_distinct_and_chain` | ✅ |
| 9 | `sum_perm_pair_factor3` | ❌ → ✅ (1 fix: simp_rw vs rw on ↔) |
| 10 | `card_distinct_triples` | ❌ → sorry'd |
| 11 | `EIntervalSize_counting` | sorry'd |

**For sub-lemmas (1–9, completing the 6-fold-symmetry machinery): 6/9 first-try ≈ 67%.**

## Build iterations

| v | Errors | Fixes |
|---|--------|-------|
| 1 | (a) wrong `linarith` step in 2-fold sub-symmetry (couldn't combine union cardinalities cleanly via `rw [hcard]`); (b) wrong contradiction pair in `hdisj_Si_Sk` (used `h1.1, h2.1` instead of `h1.2, h2.1`). | (a) Reformulated as `have hsum : card_left + card_right = card_C := ...; linarith`. (b) Identified the actual contradiction. |
| 2 | Triple-symmetry (`six_mul_permLt3Count`) compiled. Indicator factoring failed because `rw [show ↔ from ...]` ran into Decidable instance incompatibility. | Replaced with `simp_rw [h_iff]` which handles instance congruence. |
| 3 | `sum_perm_pair_factor3` compiled. Started `card_distinct_triples` and main theorem. HO-unification on nested `rw [show ∀ ...]` blocked progress. | Punted: marked both as `sorry` with detailed orchestration notes. |
| 4 | Removed unused hypotheses from `sum_perm_pair_factor3` (clean compile). | — |

## Lessons (for Session 5 and beyond)

1. **`rw [show ∀ ... from ...]` patterns frequently fail when the body involves `Finset.sum` or `if`-with-Decidable.** Always try `simp_rw` first for these. If that fails, consider `Finset.sum_congr rfl (fun x _ => ...)` for sum bodies, and `if_congr` or full case-split for if-conditions.
2. **`Finset.sum_comm` swaps adjacent sums, not arbitrary depths.** For triple-sum Fubini, plan the swap sequence carefully, or use `Fintype.sum_prod_type` to flatten.
3. **The 6-fold symmetry argument over triples is a clean generalization of C1's 2-fold pair symmetry.** The pattern (post-composition bijection by `Equiv.swap`, partition into k! ordering classes, equal cardinality) generalises to any k. **Useful for future calibration targets** that involve k-tuples of distinct indices (e.g., C4 general k, C6 variance via triples, C10 max chains).
4. **Deferring orchestration with `sorry` is honest** as long as the genuinely new mathematical content is fully proved. The 6-fold symmetry IS the new content here; the Fubini orchestration is mechanical.

## Calibration count after Session 4

| Theorem | Status | Notes |
|---------|--------|-------|
| C1 | ✅ Full | Round A |
| C2 | ✅ Full | Round B |
| C4 at k=2 | ✅ Full | Round C |
| C5 | ✅ Full incl. dim bridge | Round B + C |
| **C8** | **⚠ Sub-lemmas done, main theorem sorry'd** | **Round C, Session 4** |

**Fully done: 4 of 10. Partial: C8 (estimated ~70% complete by content).**

The Round D ≥ 5/10 gate is **not yet cleared** — C8's sorry'd main theorem doesn't count as a passed calibration target. Plan for Session 5: finish C8 (estimated 30-60 min for the Fubini orchestration), then start C3 or C6.

## Next session

1. Finish `card_distinct_triples` — likely via `Fintype.card_filter` over the product type or direct `Finset.card_prod` minus the 3-collisions count. ~15 min.
2. Finish `EIntervalSize_counting` main theorem — Fubini swap + apply sub-lemmas. ~30 min.
3. If time: start C3 (E[maximal] = H_N) using the right-to-left max reformulation. ~60-90 min.

After Session 5, calibration count should be **5 of 10 fully done**, clearing the Round D gate.
