# exp02 — C5 — P(poset dim = 2) = 1 − 1/N!

**Date:** 2026-04-28 (Session 2, Round B)
**Outcome:** ✅ Compiled, 2 build iterations (counting form). **Bridge lemma deferred.**
**Lines:** 103

## Theorem proved (counting form)

```
theorem PdimTwo_counting (N : ℕ) :
    ((Finset.univ : Finset (Perm (Fin N) × Perm (Fin N))).filter
      (fun p => p.1 ≠ p.2)).card + N.factorial = (N.factorial)^2
```

**Equivalent statement:** `#{(σ, τ) : σ ≠ τ} = (N!)² − N!`, hence
`P(σ ≠ τ) = 1 − 1/N!`. By the QG-paper bridge `is2OrderTotallyOrdered ⇔ σ = τ`
(see "Deferred bridge" below), this matches the paper's claim
`P(poset dim = 2) = 1 − 1/N!`.

## Proof structure

The diagonal of `Perm × Perm` (i.e., `{(σ, τ) : σ = τ}`) is the image of
the injection `σ ↦ (σ, σ)` over `univ : Finset (Perm (Fin N))`, which has
cardinality `N!` by `Fintype.card_perm`. The off-diagonal is the complement.
Their cardinalities sum to `|Perm × Perm| = (N!)²` by
`Finset.card_filter_add_card_filter_not`. Subtraction (after `card_diagonal_perm`
substitution into the helper) gives the claim.

## Deferred bridge

The QG paper's claim is about `dim`, not `σ = τ` directly. The bridge:

> A 2-order from `(σ, τ)` has `dim ≤ 1` (i.e., is itself a total order)
> iff `σ = τ`.

The **easy direction** `σ = τ → is2OrderTotallyOrdered` is proved here as
`diag_is_total_order`. The **hard direction** `is2OrderTotallyOrdered → σ = τ`
requires the lemma "any strictly monotone permutation of `Fin N` is the
identity," which is **not currently a one-line Mathlib lookup** (searched for
`Fintype.bijective.*StrictMono`, `OrderIso.refl`, `Fin.strictMono_eq_id`,
`Equiv.Perm.eq_one_iff_mono` — none directly hit).

Several near-relevant Mathlib results exist:

- `Mathlib/Data/Finset/Sort.lean::orderEmbOfFin_unique` — strictly monotone
  embeddings into a Finset coincide with the canonical order embedding. Can
  be used to bridge but requires setup.
- `Mathlib/Order/WellFounded.lean::Set.range_injOn_strictMono` — strict
  monotonicity uniqueness on well-founded types. Useful for the more general
  setting.

**Decision:** defer the formal bridge to a Round C session. Document it in the
file's docstring and in the PLAYBOOK as a known gap. The counting result
**is rigorous on its own** — `#{σ ≠ τ} + N! = (N!)²` is unconditional.

## Sublemmas

| # | Lemma | First-try |
|---|-------|-----------|
| 1 | `is2OrderTotallyOrdered` (def) | ✅ |
| 2 | `diag_is_total_order` (easy bridge) | ✅ |
| 3 | `card_diagonal_perm` | ❌ → ✅ |
| 4 | `card_offDiagonal_add_diagonal` | ❌ → ✅ |
| 5 | `PdimTwo_counting` (main) | ❌ → ✅ |

**Per-step verification rate: 2/5 first-try (40%).**

This is a regression vs C2's 83% — expected, because C5 uses different
proof patterns (filter on equality, image of an injection, partition by
predicate-and-its-negation) that hadn't been exercised before.

## Build iterations

| v | Errors | Fixes |
|---|--------|-------|
| 1 | (a) `refine ⟨..., ⟨trivial, ?_⟩⟩` confused with `Eq.refl`'s arity — over-anchored anonymous constructor. (b) `Finset.filter_card_add_filter_neg_card_eq_card` deprecated → use `Finset.card_filter_add_card_filter_not`. (c) `rw [← card_diagonal_perm]` rewrote BOTH `N.factorial` occurrences (LHS and RHS), leaving `N!^2 = #{p.1=p.2}^2` which `ring` couldn't close. | (a) Restructured the extensionality with `ext ⟨σ, τ⟩` + explicit case split. (b) Replaced lemma name. (c) Substituted on the helper hypothesis (`rw [card_diagonal_perm] at h1`) before using it, avoiding accidental matches in the goal. |
| 2 | None — full file compiled. | — |

## Lessons (transferable to Round C+)

1. **`refine` with anonymous constructors is fragile when the target expression is generic / unfolded.** When in doubt, use explicit case splits with `rintro`/`refine` and a body for each direction.
2. **`rw` with a lemma stating `f x = c` rewrites *every* occurrence of `c` in the goal**, including ones you didn't want. To control this, either (a) use `nth_rewrite n`, (b) substitute on a helper hypothesis first, or (c) use `show` to refocus.
3. **Mathlib deprecation warnings are informative but easy to miss in long output.** `Finset.filter_card_add_filter_neg_card_eq_card` → `Finset.card_filter_add_card_filter_not`. Worth scanning warnings even when build "succeeds" — for future-proofing, this matters.
4. **Documenting deferred lemmas** is honest and important — the QG paper claim P(dim=2) = 1−1/N! is captured here in counting form, but the formal `dim` connection requires a "monotone perm of Fin N = id" lemma we don't yet have. A `sorry`-free counting result + a documented bridge is more honest than a partial dim formalization with hidden gaps.

## Round B summary

| Theorem | Lines | Iters | Per-step | Wall-clock (chat) |
|---------|-------|-------|----------|-------------------|
| C1 | 181 | 7 | 4/7 ≈ 57% | ~30 min |
| C2 | 109 | 2 | 5/6 ≈ 83% | ~10 min |
| C5 | 103 | 2 | 2/5 ≈ 40% | ~15 min |
| **Total** | **393** | **11** | **11/18 ≈ 61%** | **~55 min** |

Aggregate per-step verification rate across Round A + Round B (3 theorems):
**11 of 18 sub-lemmas first-try (≈ 61%)**. Above the original H2 hypothesis
(>30%) and above PLAYBOOK's "low" threshold of 20%.

## Next: Round C — harder calibration targets

Per PLAYBOOK §10:

- C3: `E[maximal elements] = H_N` — needs a record-value argument.
- C4: `E[k-antichains] = C(N,k) / k!` — Stirling-ish identity.
- C6: `Var[f]` — second moment.
- C7: Tracy-Widom antichain — likely Mathlib-blocked (BDJ theorem).
- C8: `P(link)` (covering relation, no intermediates) — moderate.
- C10: `E[max chain]` — moderate.

Plus (as a separate research task) the formal bridge for C5: prove
`is2OrderTotallyOrdered σ τ → σ = τ` via the "monotone perm of Fin N = id"
lemma. Likely requires `orderEmbOfFin_unique` or a custom induction.
