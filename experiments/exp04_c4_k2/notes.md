# exp04 — C4 at k=2 — E[# 2-element antichains] = N(N−1)/4

**Date:** 2026-04-28 (Session 3, Round C)
**Outcome:** ✅ Compiled, 3 build iterations
**Lines:** 112

## Theorem proved

```
theorem ETwoAntichains_counting (N : ℕ) :
    2 * ∑ p : Perm (Fin N) × Perm (Fin N), numOrderedIncomparablePairs p.1 p.2
    = N * (N - 1) * (N.factorial)^2
```

This is C4 at k=2 in **ordered** counting form. The unordered antichain count is half the ordered count (incomparability is symmetric and `i ≠ j` is enforced via `offDiag`), so dividing by 2:
- 4 · ∑ #2-antichains = N(N−1)·(N!)², i.e., E[#2-antichains] = N(N−1)/4 = C(N,2)/2!.

The QG paper's general claim is E[# k-element antichains] = C(N, k)/k! for arbitrary k. Proving the **general k** case requires partitioning over k-subsets of `Fin N` and showing each contributes 1/k! to the expectation — that's a real Round D task. The k=2 case here is a clean corollary of C2 and serves as the calibration anchor.

## Proof structure

**Key observation:** every ordered pair `(i, j)` with `i ≠ j` is EITHER comparable (`i ≺ j ∨ j ≺ i`) OR incomparable (neither direction). The two are exclusive and exhaustive. So pointwise:

```
numOrderedIncomparablePairs σ τ + comparablePairCount σ τ = N(N-1)
```

Sum over `(σ, τ)`:
```
∑ inc + ∑ comp = (N!)² · N(N-1)
```

C2 (Round B) gives `2 · ∑ comp = N(N-1) · (N!)²`, so `∑ comp = N(N-1) · (N!)² / 2`. Substituting:
```
∑ inc + N(N-1)·(N!)²/2 = (N!)²·N(N-1)
∑ inc = (N!)²·N(N-1) - N(N-1)·(N!)²/2 = N(N-1)·(N!)²/2
2·∑ inc = N(N-1)·(N!)²  ∎
```

The Lean proof keeps everything in ℕ (no division) by working with the doubled form throughout.

## Sublemmas

| # | Lemma | First-try |
|---|-------|-----------|
| 1 | `numOrderedIncomparablePairs` (def) | ✅ |
| 2 | `ite_not_add_ite` | ✅ |
| 3 | `incomparable_plus_comparable_indicator` | ✅ |
| 4 | `incomparable_plus_comparable_eq` | ❌ → ✅ (1 fix) |
| 5 | `ETwoAntichains_counting` (main) | ❌ → ✅ (2 fixes) |

**Per-step verification rate: 3/5 first-try (≈ 60%).**

## Build iterations

| v | Errors | Fixes |
|---|--------|-------|
| 1 | (a) `rw [show ∀ p, ...]` HO unification: pattern `numOrderedIncomparablePairs ?p.1 ?p.2 + ...` not matched in `∑ p, (... p.1 p.2)`. (b) `ring_nf at h2sum hC2 ⊢; linarith` fails because the goal `2 * (N!*N!*(N*(N-1))) = 2 * (N!^2 * (N*(N-1)))` is non-linear. | (a) Replaced with explicit `Finset.sum_congr rfl (fun p _ => h_pointwise p)` after building `h_pointwise : ∀ p ∈ univ, ... = ...`. (b) Switched to `set` bindings (Sinc, Scomp, K) and used `linarith` after one `ring`-derived auxiliary equation. |
| 2 | `N.factorial * N.factorial * (N * (N - 1)) = N.factorial ^ 2 * (N * (N - 1))` unsolved. | Added explicit `ring` after the rewrites. |
| 3 | None — full file compiled. | — |

## Lessons (transferable, Round C+)

1. **For "sum of f equals constant": don't use `rw [show ∀ p, ... from ...]`.** Use `Finset.sum_congr rfl h_pointwise` where `h_pointwise : ∀ p ∈ s, f p = c`. Cleaner and works with HO unification.
2. **`ring_nf` + `linarith` doesn't close non-linear goals.** When the conclusion involves products of three or more variables (like `N * (N-1) * N!^2`), use `set` to introduce abbreviations (`Sinc`, `Scomp`, `K`), prove a small identity to align the abbreviations (e.g., `K = N!^2 * (N*(N-1))`), then `linarith` over the abbreviated form. This separates the algebra from the proof structure.
3. **Mathlib's `Finset.sum_const` gives `∑ x ∈ s, c = s.card • c`** — note the `smul` not `*`. Convert with `smul_eq_mul`. Then chase `Finset.card_univ` → `Fintype.card_prod` → `Fintype.card_perm` → `Fintype.card_fin` to reach `(N!)²`.

## Round C cumulative tally

After this session:

| Theorem | Round | Lines | Iters | First-try | Status |
|---------|-------|-------|-------|-----------|--------|
| C1 (ordered pair count) | A | 181 | 7 | 4/7 ≈ 57% | ✅ |
| C2 (ordering fraction) | B | 109 | 2 | 5/6 ≈ 83% | ✅ |
| C5 counting form | B | 103 | 2 | 2/5 = 40% | ✅ |
| C5 dim bridge | C | +48 | 2 | 3/4 ≈ 75% | ✅ (full proof) |
| C4 at k=2 | C | 112 | 3 | 3/5 = 60% | ✅ (k=2 only) |

**Aggregate Round A+B+C: 17 / 27 sublemmas first-try ≈ 63%.** Stable across rounds.

**Calibration count: 4 of 10 done** (C1, C2, C4@k=2, C5).
- C5 includes the full dim bridge → dim claim formally proved.
- C4 at k=2 is the simplest k case; general k is a Round D task.
- One more theorem clears the Round D ≥ 5/10 gate.

## Round C + Round D plan

For the next session:
1. **C8 (P(link))** — covering relation, no intermediates. Moderate complexity. Likely the easiest path to 5/10.
2. **C3 (E[maximal] = H_N)** — needs ℚ machinery and right-to-left max reformulation. Significant new infrastructure. Time-box one session to attempt.
3. **C4 general k** — partition over k-subsets, show each is 1/k! antichain. Requires more sophisticated combinatorics.
4. **C6 (Var[f])** — second-moment computation; reuse C1's `permLtCount` machinery for triple covariance. Probably moderate.
5. **C10 (E[max chain])** — moderate. Needs chain combinatorics.

C7 (Tracy-Widom) and C9 (Hasse connectivity) remain Mathlib-blocked. Defer.
