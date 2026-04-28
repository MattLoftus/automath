# Novelty check

**Date:** 2026-04-28 (Round B / Session 2)
**Searched by:** Claude Code (this session) via WebSearch
**Verdict:** **Proceed.** No close prior art on the specific angle — `LLM-driven Lean formalization calibrated on random 2-orders / random partial-order combinatorics`. Several adjacent works exist and must be cited in the methods paper.

## Search queries used

1. `Lean 4 LLM extremal combinatorics random poset formalization 2025 2026`
2. `"random partial order" OR "random 2-order" Lean Mathlib formalization`
3. `Claude OR ChatGPT Lean theorem prover extremal combinatorics calibration benchmark 2026`
4. `Cambridge Part III Lean Mathlib "extremal" "probabilistic combinatorics" formalization random poset`

## Adjacent prior work (must be cited)

### CombiBench (Liu et al., arXiv:2505.03171, May 2025)

**The closest direct competitor.** A 100-problem Lean 4 benchmark covering "10+ combinatorial topics," ranging from middle school to IMO and university level. Best performer: Kimina-Prover at 7/100 solved. Tests multiple LLMs without task-specific fine-tuning.

**Differences from AutoMath:**
- **Olympiad / contest focus**, not research math. CombiBench's stated goal is "testing IMO solving capabilities." AutoMath calibrates on the author's own published research-level identities (QG Paper G), which is a different evaluation regime.
- **Random partial orders / 2-orders not covered.** CombiBench's topic list does not include them. Our calibration substrate (uniform 2-orders on `Fin N` with expectations of `link count`, `ordering fraction`, `dim`, `antichain count`, `H_N` formulas, etc.) is not in their set.
- **Benchmark-evaluation methodology.** CombiBench tests fixed-prompt LLMs on a frozen problem set; AutoMath is a working pipeline that incrementally formalizes one researcher's own theorems with iterative compiler feedback.
- **Architecture.** CombiBench uses Kimina Lean Server backend with various LLMs (DeepSeek-Prover-V2, Seed-Prover, Kimi K2, Gemini-3 Pro). AutoMath uses Claude Code as the agent loop with no external orchestration.

CombiBench is the right baseline to cite for "what's the going rate for combinatorics in Lean today" — they hit 7% on a 100-problem set with prover-style models. Our per-step verification rate on the calibration set is the comparable metric.

### LeanCamCombi (Yaël Dillies, ongoing)

GitHub: https://github.com/YaelDillies/LeanCamCombi. Formalizes Cambridge Part II and Part III courses on Graph Theory, Combinatorics, Extremal and Probabilistic Combinatorics in Lean. Erdős–Rényi binomial random graphs under active development. Backed by Mathlib.

**Differences from AutoMath:**
- **Course material, not research-level identities.** LeanCamCombi formalizes the lecture content of Sahasrabudhe's Part III; we calibrate on novel published QG-Paper-G results.
- **Hand-formalized, not LLM-driven.** LeanCamCombi appears to be hand-written by the maintainer. AutoMath is a Claude-Code-as-agent workflow.
- **Random 2-orders not present** (only random graphs). Our domain is genuinely different — 2-orders are intersections of two total orders, with very different combinatorial structure than Erdős–Rényi graphs.

### Tao's Claude Code + Lean workflow (2026 talks, blog posts)

YouTube talk + Hacker News thread: https://news.ycombinator.com/item?id=47306852. Tao formalizing his own Analysis-I-style proofs interactively with Claude Code, decomposing into sub-lemmas before delegation.

**Differences from AutoMath:**
- **Different mathematical domain** — analysis, not combinatorics.
- **Different research focus** — Tao demonstrates the workflow; we measure per-step verification rate as a function of Mathlib coverage.
- **Stylistic anchor, not a competitor.** Tao's posts are the closest public template for the AutoMath workflow. We will cite as the methodological precedent.

### Construction-Verification benchmark (arXiv:2602.01291, 2026)

A benchmark for formalizing applied mathematics in Lean 4. Surfaced by search; topics overlap with engineering / applied analysis. Less directly related to extremal combinatorics. **Cite for completeness; not a direct competitor.**

### IndiMathBench (arXiv:2512.00997, December 2025)

Autoformalizing mathematical reasoning. Surfaced by search; methodology is autoformalization at scale. Less directly related to research-level combinatorics.

### Galois Inc. — "Claude Can (Sometimes) Prove It" (2026)

Industry blog post on Claude's ITP capabilities. Anecdotal evidence aligned with our experience. Not a peer-reviewed contribution.

### Knuth ↔ Claude Opus 4.6 combinatorics problem (2026)

Claude solved an open combinatorics problem of Knuth's in ~1 hour, with Knuth's assessment that the structure was sound and rigorous. Indicates the "Claude on combinatorics" angle is being actively demonstrated. Cite as additional anecdotal evidence.

## Distilled differentiation

AutoMath's defensible novelty:

1. **Calibration substrate is the author's own published peer-reviewed work** — QG Paper G, 15+ exact identities, all hand-proved, all small-N-numerically-verified. Reproducible ground truth in a way contest benchmarks aren't.
2. **Domain: random 2-orders specifically.** Not in any current Lean-combinatorics project.
3. **Counting-form methodology.** Avoids Mathlib's measure-theory infrastructure gap by phrasing claims as `Finset` counting identities. This may itself be reusable.
4. **Architecture: Claude Code as agent loop, no external orchestration, no API budget.** Differentiated from CombiBench's prover-server backend and from Tao's interactive demonstrations (which use API).
5. **Independent-lab + low-budget framing.** Counters the DeepMind / OpenAI scale assumption.

## Verdict

**No kill.** Proceed to Round D (broader calibration). Document CombiBench, LeanCamCombi, and Tao's workflow as related work in the methods paper, with explicit comparison of methodology and scope.

## Required citations for methods paper

- CombiBench (Liu et al., 2025)
- LeanCamCombi (Dillies, 2024–ongoing)
- Tao's Claude Code + Lean talks (2026)
- Mathlib4 (community)
- Polu & Sutskever 2020 (GPT-f)
- Jiang et al. 2022 (Thor)
- First et al. 2023 (Baldur)
- Trinh et al. 2024 (AlphaGeometry)
- Weng et al. 2024 (AlphaProof)

## Re-check trigger conditions

Re-run novelty check at:
1. End of Round D (before paper draft).
2. End of Round F (before submission).
3. If Tao or another researcher publishes a paper specifically on Lean+LLM for random partial orders.
