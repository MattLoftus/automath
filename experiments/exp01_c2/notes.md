# exp01 — C2 — Expected ordering fraction E[f] = 1/2

**Date:** 2026-04-28 (Session 2, Round B)
**Outcome:** ✅ Compiled, 2 build iterations
**Lines:** 109

## Theorem proved (counting form)

```
theorem EOrderingFraction_counting (N : ℕ) :
    2 * ∑ p : Perm (Fin N) × Perm (Fin N), comparablePairCount p.1 p.2
    = N * (N - 1) * (N.factorial)^2
```

Where `comparablePairCount σ τ` is the number of ordered pairs `(i, j)` with `i ≠ j`
such that `i ≺ j` or `j ≺ i` in the 2-order from `(σ, τ)`. Equivalent statement:
`E[f] = 1/2` under the uniform distribution on `Perm × Perm`, since
`f = comparablePairCount / [N(N-1)]`.

## Proof structure

C2 reduces to C1 by showing `comparablePairCount = 2 · orderedPairCount`. The
disjunction `i≺j ∨ j≺i` is disjoint (since `<` is irreflexive), so its indicator
is the SUM of the two strict indicators. The "j≺i" sum reindexes to the "i≺j"
sum via the swap bijection `(i, j) ↔ (j, i)` on `offDiag`. Then 2 · ∑ comparable
= 2 · ∑ (2 · ordered) = 4 · ∑ ordered = N(N−1) · (N!)² by C1.

## Sublemmas used

| # | Lemma | First-try |
|---|-------|-----------|
| 1 | `ite_or_disjoint_eq_add` | ✅ |
| 2 | `comparablePairCount` (def) | ✅ |
| 3 | `compr_disjoint` | ✅ |
| 4 | `sum_swap_offDiag` | ❌ → ✅ (1 fix) |
| 5 | `comparablePairCount_eq_two_orderedPairCount` | ✅ |
| 6 | `EOrderingFraction_counting` (main) | ✅ |

**Per-step verification rate: 5/6 first-try (≈ 83%).**

## Build iterations

| v | Errors | Fix |
|---|--------|-----|
| 1 | `apply Finset.sum_bij'` matched goals in unexpected order — second `·` block landed on `left_inv` instead of `hj`. Mechanically: the inverse step had goal `((p.2, p.1).2, (p.2, p.1).1) = p` while my code expected `(p.2, p.1) ∈ univ.offDiag`. | Switched to `Finset.sum_nbij'` (non-dependent) with `Prod.swap` and `Prod.swap_swap`. Goals matched in the expected order; `rfl` closed the value-match. |
| 2 | None — full file compiled. | — |

## Lessons (transferable to Round C)

1. **`Finset.sum_bij'` produces goals in an order I didn't predict.** Switching to `Finset.sum_nbij'` with `Prod.swap` and Mathlib's `Prod.swap_swap` was much cleaner — no membership-proof bureaucracy in the bijection, just plain functions. **Use `sum_nbij'` whenever the bijection doesn't actually need membership info.**
2. **The "swap (i,j) ↔ (j,i) on offDiag" is a recurring pattern** in 2-order counting arguments. The `sum_swap_offDiag` lemma here is reusable for any future 2-order theorem that reindexes via element-pair swap (e.g., C6's variance computation).
3. **Reusing C1's `orderedPairCount` definition compounded — the C2 proof is half the size of C1's** (109 vs 181 lines) because the heavy machinery was already there. This is the calibrate-then-extend pattern paying off.

## Round B per-step verification trend (running)

- C1: 4/7 first-try ≈ 57%, 7 build iterations
- C2: 5/6 first-try ≈ 83%, 2 build iterations

Trend is positive. C1 included a lot of "first time using Mathlib X" overhead; C2 mostly reused the C1 patterns. C5 should give us the next data point on a proof that's structurally different (filter-on-disjunction + diagonal counting) — expect a regression vs C2 since the patterns are new.

## Next: C5 (this session) → exp02_c5/notes.md.
