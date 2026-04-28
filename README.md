# AutoMath

Claude Code + Lean 4 + Mathlib pipeline for formalizing extremal-combinatorics
theorems, calibrated on QG Paper G's 15+ published identities for random 2-orders.

**Stack:** Lean 4 v4.30.0-rc2 + Mathlib v4.30.0-rc2 (math-lax template) +
Claude Code as the agent loop. No Anthropic-API orchestration. No embedding RAG.

**Status (2026-04-27):** Round A complete. C1
(`E[# ordered comparable pairs] = N(N−1)/4`) formalized in counting form:
`4 · Σ orderedPairCount = N(N−1) · (N!)²`. See
`lean/Automath/QGPaperG/C1_OrderedPairCount.lean`.

**Full plan:** see [PLAYBOOK.md](PLAYBOOK.md).
**Kickoff prompt for a fresh Claude chat:** see [KICKOFF_PROMPT.md](KICKOFF_PROMPT.md).

## Quickstart

```bash
# 1. Install Lean 4 via elan (non-interactive).
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan default leanprover/lean4:stable

# 2. Build the project (also pulls Mathlib's prebuilt cache on first run).
cd lean
lake build
```

Theorems live under `lean/Automath/QGPaperG/`. Add `import Automath.QGPaperG.<NewFile>`
to `Automath.lean` to include them in the build target.
