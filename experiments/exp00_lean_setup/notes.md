# exp00 — Session 1 — Lean stack live + C1 hand-formalized

**Date:** 2026-04-27
**Session length:** ~one Claude Code chat
**Outcome:** Round A of PLAYBOOK complete

## What happened

Eight tasks ran end-to-end:

1. Read all orientation files (SOUL, CLAUDE, RESEARCH_LEARNINGS, QG Paper G theorem statements, this PLAYBOOK).
2. Architectural pivot — dropped Anthropic-API + Python-orchestration + embedding-RAG plumbing in favour of Claude-Code-as-agent. Saved `feedback_claude_code_as_agent_loop.md` to memory.
3. Installed elan via `elan-init.sh`. Set default toolchain to `leanprover/lean4:stable` (resolves to v4.30.0-rc2). PATH note: elan added itself to `~/.bash_profile` but the Bash tool's non-login shell needs `export PATH="$HOME/.elan/bin:$PATH"` per call.
4. Initialized Lake project at `~/workspace/automath/lean/` with `lake init Automath math-lax.toml`. Template auto-pulled Mathlib v4.30.0-rc2 and ran `lake exe cache get` — downloaded 8,297 prebuilt `.olean` files (~5 minutes).
5. Verified: `HelloMath.lean` compiles via `lake env lean HelloMath.lean`. `lake build` clean.
6. Surveyed `Mathlib/Combinatorics/` subdirectory structure and the relevant primitives for C1.
7. Hand-formalized C1 in counting form. 181 lines of Lean (including ~25-line docstring). 7 build iterations to a fully-typechecked file.
8. Initialized git, pushed public to `MattLoftus/automath`.

## C1 — what was actually proved

```
theorem ELinkCount_counting (N : ℕ) :
    4 * ∑ p : Perm (Fin N) × Perm (Fin N), orderedPairCount p.1 p.2
    = N * (N - 1) * (N.factorial)^2
```

Where:

```
def orderedPairCount (σ τ : Perm (Fin N)) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
    (if σ p.1 < σ p.2 ∧ τ p.1 < τ p.2 then 1 else 0)
```

The "counting form" framing — ∑ over (σ, τ) instead of E[·] under the uniform distribution — was the right call. It avoids any measure theory and lives entirely in `Finset` + `Equiv.Perm`, which Mathlib supports very well. The probability statement `E[orderedPairCount] = N(N−1)/4` is a one-line corollary once a `uniformDist on Perm` wrapper exists, but we did not need that wrapper for the calibration.

**Naming correction** vs. PLAYBOOK §6: the original called this "C1: E[link count] = N(N−1)/4". In QG Paper G, "link" means a covering relation (no intermediate elements), which is a different (and harder) object. The N(N−1)/4 formula is for **ordered comparable pairs** (i.e., ordered pairs (i,j) with i ≠ j and i ≺ j). The PLAYBOOK §6 entry has been corrected.

### Proof structure (5 sublemmas + main theorem)

| # | Lemma | Role | First-try compile |
|---|-------|------|-------------------|
| 1 | `permLtCount` | def: count of σ with σ i < σ j | n/a |
| 2 | `two_mul_permLtCount` | the swap-symmetry lemma: 2 · permLtCount = N! | ❌ (3 iterations: bij injectivity beta-reduction, partition-cardinality rewrite chain) |
| 3 | `card_offDiag_fin` | offDiag of `Fin N` has card `N(N−1)` | ❌ (2 iterations: `omega` couldn't see through `(n+1)*(n+1) − (n+1)` without an explicit ring step) |
| 4 | `orderedPairCount` | def: sum of joint indicators over `Fin N`'s offDiag | ✅ |
| 5 | `ite_and_eq_mul` | ⟦P ∧ Q⟧ = ⟦P⟧ · ⟦Q⟧ in ℕ | ✅ |
| 6 | `sum_indicator_eq_permLtCount` | ∑_σ ⟦σ i < σ j⟧ = permLtCount i j (in ℕ) | ✅ |
| 7 | `sum_perm_pair_factor` | the joint sum factors into a product of marginals | ❌ (3 iterations: `Fintype.sum_mul_sum` higher-order unification) |
| 8 | `ELinkCount_counting` | main theorem | ❌ (1 iteration: extra rewrite) |

Per-step auto-verification rate (this theorem): **3 of 6 proof obligations first-try, ≈ 50%.** If we count the main theorem's own iteration, ≈ 4 of 8 — about 57%.

### Lean-specific gotchas encountered

These are recurring patterns I expect to hit again. Worth keeping a checklist for Round B+.

1. **Lambda binders in `Finset.card_bij'` pollute the injectivity hypothesis.** When you pass `(fun σ _ => σ * Equiv.swap i j)` to `card_bij'`, the hypothesis comes back as `(fun σ x ↦ σ * swap i j) σ₁ ha₁ = (fun σ x ↦ σ * swap i j) σ₂ ha₂`. Need `simp only at h` to beta-reduce before `mul_right_cancel`.
2. **`Finset.card_univ` then `Fintype.card_perm`, in that order.** `#univ` for a Fintype is `(Finset.univ : Finset α).card`, which is NOT directly `Fintype.card α`; you have to go through `Finset.card_univ` first.
3. **`omega` does NOT see through nat multiplication.** For `(n+1)*(n+1) − (n+1) = (n+1)*n`, you need an explicit ring step: `have : (n+1)*(n+1) = (n+1)*n + (n+1) := by ring; omega`.
4. **`Finset.sum_boole` is generic over a Semiring R, with a `Nat.cast`.** When the target type is pure ℕ, the cast is identity but the rewrite engine doesn't see through it. Use `Finset.card_eq_sum_ones` + `Finset.sum_filter` instead, or pass `(R := ℕ)` explicitly.
5. **`Fintype.sum_mul_sum` needs explicit `f` and `g` for higher-order unification.** Writing `rw [← Fintype.sum_mul_sum]` against `∑ x, ∑ y, (if x i < x j then 1 else 0) * (if y i < y j then 1 else 0)` fails — Lean can't abstract the inner expressions automatically. Instantiate manually: `(Fintype.sum_mul_sum (fun x => ...) (fun y => ...)).symm`.
6. **`lake build` reuses the Mathlib cache cleanly.** First build of a new file is ~30–70s (most of which is loading the import). Subsequent builds of unchanged files are skipped.

## Mathlib4 combinatorics map (skim)

`lean/.lake/packages/mathlib/Mathlib/Combinatorics/`:

```
Additive/        — additive combinatorics (Plünnecke, sumsets)
Derangements/    — derangement permutations
Digraph/         — directed graphs
Enumerative/     — generating functions, Stirling, partitions
Extremal/        — extremal graph theory ← potentially useful for stretch goals
Graph/, SimpleGraph/, Hall/, SetFamily/  — graph-y
Matroid/         — matroids
Optimization/    — combinatorial optimization
Quiver/          — directed multigraphs / categories
Tiling/          — tilings
Young/           — Young tableaux

Pigeonhole.lean, HalesJewett.lean, KatonaCircle.lean, Hindman.lean, Schnirelmann.lean,
Nullstellensatz.lean, Configuration.lean, Compactness.lean, Colex.lean
```

Key permutation infrastructure NOT under Combinatorics — under `GroupTheory/Perm/`:
- `Perm/Basic.lean` — `Equiv.Perm` API
- `Perm/Sign.lean` — signature, alternating sign formula
- `Perm/Subgroup.lean` — symmetric-group as group
- `Perm/Cycle/Basic.lean` — cycle decomposition
- `Perm/Fin.lean` — perms of Fin N specifically; sign formula via inversion count

And random-poset / 2-order / random partial-order infrastructure: **none yet.** That is consistent with the PLAYBOOK's expectation. If we want a `uniformDist on Perm` wrapper for the probability framing, we'll need to build it.

## Tao Lean+Claude reading list

Verified by web search 2026-04-27. URLs as plain text (terminal blue is unreadable).

- **Tao 2026-03 — Formalizing a proof in Lean using Claude Code.** YouTube + HN thread at news.ycombinator.com/item?id=47306852. The closest public match for our workflow. Tao's first attempt ran 45 min + crashed; second attempt 25 min after decomposing into hand-defined sub-lemmas. We hit the same shape on C1 (one-shot doesn't work; decompose, hand the skeleton to Claude, fix per-error).
- **Tao 2025-05-31 — "A Lean companion to Analysis I."** terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/. Long-form formalization. Stylistic anchor for proof file structure.
- **Tao 2024-03 — "Machine assisted proofs."** terrytao.wordpress.com/wp-content/uploads/2024/03/machine-jan-3.pdf. Big-picture framing.
- **teorth/analysis on GitHub.** Public repo for the Analysis I work. Skim for naming + structure conventions.
- **Equational Theories Project (Tao 2024).** Lean + ATPs settling 22M+ universal-algebra problems.

## Decisions for Session 2

1. **Next theorem: C2 (E[ordering fraction f] = 1/2).** Should reduce to a one-line corollary of C1 (or vice versa, since `f = R/(N(N−1))` and `R = 2 · orderedPairCount`).
2. **Then C5 (P(poset dim = 2) = 1 − 1/N!).** Uses a different argument (free action of S_N), so it's a real second data point.
3. **Mandatory novelty check at end of Session 2.** Search arXiv `cs.LO` + `math.CO` and Lean Zulip for "extremal combinatorics" + "Lean" + "LLM" or "agent." Document at `papers/novelty_check.md`.
4. **Per-theorem stats logged in dedicated dirs.** `experiments/exp01_c2/`, `experiments/exp02_c5/`. Track per-step verification rate, total iterations, wall-clock, lines of Lean.
5. **No premature pipelining.** Resist the temptation to add a Python orchestrator after a few theorems — Claude Code IS the pipeline. Only add automation if multiple theorems run cleanly without human guidance.

## Files created or modified this session

- `lean/lakefile.toml` — Mathlib v4.30.0-rc2 dependency
- `lean/lean-toolchain` — leanprover/lean4:v4.30.0-rc2
- `lean/HelloMath.lean` — sanity-check
- `lean/Automath.lean` — root module imports
- `lean/Automath/QGPaperG/C1_OrderedPairCount.lean` — ✅ the actual result
- `PLAYBOOK.md` — fully updated to no-API architecture, compressed timeline, marked Round A complete
- `README.md` — updated status + quickstart
- `experiments/exp00_lean_setup/notes.md` — this file
- `~/.claude/projects/-Users-Loftus/memory/feedback_claude_code_as_agent_loop.md` — new memory entry
- `~/.claude/projects/-Users-Loftus/memory/MEMORY.md` — index updated
