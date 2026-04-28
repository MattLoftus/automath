# exp03 — C5 dim bridge — `is2OrderTotallyOrdered ⇔ σ = τ`

**Date:** 2026-04-28 (Session 3, Round C)
**Outcome:** ✅ Compiled, 1 build iteration after the initial draft
**Lines added:** ~50 (appended to `C5_DimensionTwo.lean`, file now 151 lines)

## What was deferred from Round B and now closed

Round B's C5 file proved `#{σ ≠ τ} + N! = (N!)²` (the counting form) but **deferred the bridge** that connects this to the dim claim. Specifically: P(dim = 2) = 1 − 1/N! requires that the 2-order from `(σ, τ)` has dim ≤ 1 (i.e., is itself a total order) iff `σ = τ`. The easy direction was proved as `diag_is_total_order`. The hard direction — `is2OrderTotallyOrdered → σ = τ` — was the gap.

## What was proved in Session 3

```lean
lemma totallyOrdered_imp_eq (σ τ : Perm (Fin N)) (h : is2OrderTotallyOrdered σ τ) :
    σ = τ

theorem isTotallyOrdered_iff_eq (σ τ : Perm (Fin N)) :
    is2OrderTotallyOrdered σ τ ↔ σ = τ
```

Combined with `diag_is_total_order`, the iff statement gives the full bridge. C5's PdimTwo_counting + the bridge now give the complete QG paper claim P(dim = 2) = 1 − 1/N!.

## The proof

**Key idea:** `σ * τ⁻¹ : Equiv.Perm (Fin N)` is strictly monotone under the `is2OrderTotallyOrdered` hypothesis, hence the identity.

**Step 1:** show `StrictMono (σ * τ⁻¹)`. For any `a < b` in `Fin N`, the pair `(τ⁻¹ a, τ⁻¹ b)` is in `offDiag` (since `τ⁻¹` is injective and `a ≠ b`). The hypothesis applied to this pair gives a disjunction:
- Either `σ (τ⁻¹ a) < σ (τ⁻¹ b) ∧ τ (τ⁻¹ a) < τ (τ⁻¹ b)` — the σ-direction is what we want.
- Or `σ (τ⁻¹ b) < σ (τ⁻¹ a) ∧ τ (τ⁻¹ b) < τ (τ⁻¹ a)` — but `τ (τ⁻¹ a) = a < b = τ (τ⁻¹ b)`, contradicting the τ-direction in this case.

**Step 2:** apply `Mathlib/Order/WellFounded.lean::StrictMono.range_inj`. For two strictly monotone functions on a `WellFoundedLT` type, equal range ⇒ equal functions. We have `Set.range (σ * τ⁻¹) = Set.univ` (because `σ * τ⁻¹` is an `Equiv.Perm`, hence a bijection — `Equiv.range_eq_univ`) and `Set.range id = Set.univ` (`Set.range_id`). Hence `(σ * τ⁻¹ : Fin N → Fin N) = id`.

**Step 3:** `Equiv.ext` upgrades the function-equality to `Equiv.Perm`-equality. So `σ * τ⁻¹ = 1` in the group `Equiv.Perm (Fin N)`. Apply `mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b` to conclude `σ = τ`.

## Mathlib lemmas used

- `Equiv.apply_symm_apply : e (e.symm x) = x` — to simplify `τ (τ⁻¹ a) = a`. Needed `show τ (τ.symm a) = a` first to convert `_⁻¹` (group inverse) to `.symm` (Equiv inverse), since they're definitionally equal but `simp` doesn't always unfold the group-inverse.
- `StrictMono.range_inj` — equal range ⇒ equal function for two strict-mono functions on a `WellFoundedLT` type.
- `Equiv.range_eq_univ` — the range of any `Equiv` is `Set.univ`.
- `Set.range_id`, `mul_inv_eq_one`, `Equiv.ext`.

## Build iterations

| v | Errors | Fixes |
|---|--------|-------|
| 1 | (a) `Unknown constant Equiv.Perm.apply_inv_self` — wrong lemma name. (b) `lt_asymm hab` typed as `a < b → ¬ (b < a)` doesn't match `τ (τ⁻¹ b) < τ (τ⁻¹ a)`. | Replaced with `show τ (τ.symm x) = x; exact τ.apply_symm_apply x` for both direction. Then `rw [...]` resolves the type mismatch. |
| 2 | None — full file compiled. | — |

## Per-step verification rate

The bridge has 4 logical sub-pieces inside `totallyOrdered_imp_eq`:
1. Define φ := σ * τ⁻¹ ✅ first-try
2. Prove StrictMono φ ❌ → ✅ (1 fix: `apply_inv_self` rename)
3. Prove φ as a function = id ✅ first-try (using `range_inj`)
4. Conclude σ = τ via `Equiv.ext` and `mul_inv_eq_one` ✅ first-try

The wrapper iff `isTotallyOrdered_iff_eq` is a one-liner. So ~3 of 4 internal steps first-try (~75%).

## Lessons (transferable)

1. **Group inverse `_⁻¹` for `Equiv.Perm` doesn't auto-unfold to `.symm`.** When applying `Equiv.apply_symm_apply` to a goal of form `τ (τ⁻¹ x)`, you need an explicit `show τ (τ.symm x) = x` to convert the syntactic form before `simp`/`exact` works. This is recurring and worth remembering for future Equiv.Perm proofs.
2. **`StrictMono.range_inj` is the right tool for "monotone bijection of finite linear order = id".** Mathlib doesn't have a one-line `Fin.strictMono_eq_id` lemma, but `range_inj` + `Equiv.range_eq_univ` + `strictMono_id` composes cleanly. ~3 lines once you know the pattern.

## C5 status now

✅ **Counting form** (`#{σ ≠ τ} + N! = (N!)²`) — Round B (Session 2).
✅ **Easy bridge** (`σ = τ → is total order`) — Round B (Session 2).
✅ **Hard bridge** (`is total order → σ = τ`) — Round C (Session 3).
✅ **Full iff** (`isTotallyOrdered_iff_eq`) — Round C (Session 3).

C5's QG-paper claim P(dim = 2) = 1 − 1/N! is now fully formalized.
