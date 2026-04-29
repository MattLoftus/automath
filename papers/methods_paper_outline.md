# AutoMath Methods Paper — Outline

**Working title:** "Claude Code as the Agent Loop: Per-Step Verification Rate of LLM-Driven Lean 4 Formalization in Extremal Combinatorics"

**Target venues:**
- Primary: JAR (Journal of Automated Reasoning) or ITP (Interactive Theorem Proving conference).
- Alternate: J. Symb. Logic, JACM, TACAS.
- arXiv: stat.ML primary (Mahoney endorsement), cs.LO + math.CO cross-list.

**Estimated length:** 8–12 pages.

## Section outline

### 1. Introduction (1 page)
- The state of LLM + formal proof assistant integration: AlphaProof, AlphaGeometry, Tao's Claude Code workflow, CombiBench (May 2025).
- The gap: per-step verification rate as a function of theorem complexity in a SPECIFIC research domain has not been measured.
- Our contribution: calibrate Claude Code + Lean 4 + Mathlib on QG Paper G (Loftus 2026), 5 of 10 published identities formalized; report per-step rates; demonstrate the same workflow extends to a NEW exact value at N=6 (Round E).

### 2. The pipeline as Claude Code (1 page)
- No external orchestration: Claude Code IS the agent loop.
- Architecture diagram (from PLAYBOOK §5.1).
- Comparison vs. CombiBench's Kimina-Prover backend, vs. Tao's interactive workflow.
- Cost: existing Claude Code subscription, no Anthropic API spend.

### 3. The calibration substrate: QG Paper G (1 page)
- Background on random 2-orders (Loftus 2026, "Exact combinatorial results for random 2-orders").
- 15+ identities; we attempt 10 (C1–C10), defer C7 (Tracy-Widom, BDJ-blocked) and C9 (Hasse, Mathlib-coverage-blocked).
- Why this domain: Mathlib has most of the primitives (Equiv.Perm, Finset.offDiag, Fintype.card_perm); the gaps are filled by hand-formalized lemmas.

### 4. Calibration results (3 pages)
- Table 1: per-theorem stats (lines, build iterations, sub-lemmas first-try, wall-clock).
  - C1: 181 lines, 7 iters, 4/7 ≈ 57% first-try
  - C2: 109 lines, 2 iters, 5/6 ≈ 83% first-try
  - C4@k=2: 112 lines, 3 iters, 3/5 = 60% first-try
  - C5: 151 lines, 4 iters total (Round B + Round C bridge), 5/9 ≈ 56% first-try
  - C8: 460 lines, 7 iters, 11/16 ≈ 69% first-try
- Aggregate per-step verification rate: ~63% across 30+ sublemmas.
- Discussion: where the 37% errors live (HO unification, Decidable instance issues, `simp` non-progress, deprecated lemma names). Catalog of recurring Lean gotchas.
- Comparison: CombiBench reports 7/100 ≈ 7% on contest-math problems with prover-style models; our 63% per-sub-lemma on research-math is in a different regime — but the comparison should be honest about the differences (we use Mathlib retrieval; they're zero-shot).

### 5. Methodological choices (1 page)
- Counting form vs. probability form: every theorem stated as a sum identity in ℕ, avoiding Mathlib's measure-theory infrastructure for "uniform on Sym(N)". Each `E[X] = a/b` claim becomes `b · ∑ X = a · |Sym(N)²|`.
- Cite C5 specifically as showing this approach works even for dimension claims (P(dim = 2) = 1 − 1/N!) once a small bridge lemma (`is2OrderTotallyOrdered ⇔ σ = τ`) is proven.
- Reuse of machinery across theorems: C1's `permLtCount` reused in C2, C8; C8's `permLt3Count` reusable in C6 (variance) and C4 general k.

### 6. Round E: a new exact value at N=6 (2 pages)
- The QG paper computes E[|Aut|] for N=2,3,4,5: 3/2, 13/6, 71/24, 89/24.
- We compute N=6: **E[|Aut|] = 349/80 = 4.3625** (new).
- Method: Python brute-force enumeration over (Sym(6))² with caching by 2-order shape (~21.6 s on M4 Pro). N=2..5 verified against Loftus's hand calculations.
- External cross-check: unique 2-order shape count matches OEIS A001035 (labeled posets) for N=2..5; at N=6, the difference of 840 equals the known number of dim-3 labeled posets first appearing at N=6.
- Lean formalization: N=2..5 kernel-verified via `native_decide`. N=6 stated as `axiom` — `native_decide` killed at ~10 min CPU due to 1.3 · 10¹⁰ operations through `Equiv.Perm (Fin 6)` machinery. Discuss the trade-off honestly.
- (If N=7 lands) Round E extension: N=7 compute, sequence analysis.

### 7. Methodology critique and limitations (1 page)
- 5/10 calibration ≠ 10/10. Discuss what the un-formalized targets (C3 harmonic, C6 variance, C4 general k, C10) would add and why we stopped at 5.
- The `axiom`-for-N=6 decision: not kernel-checked but reproducibly Python-verified. Reference: Four Color Theorem (Appel-Haken 1976) was originally external; Coq formalization (Gonthier 2005) came much later via different methods.
- The pipeline's dependence on Mathlib coverage. Two of our targets (C7, C9) are Mathlib-blocked (Tracy-Widom and Hasse-connectivity infrastructure both missing).

### 8. Related work (1 page)
- CombiBench (Liu et al., May 2025): 100-problem contest combinatorics benchmark in Lean 4. Different regime from research math.
- LeanCamCombi (Dillies, ongoing): Cambridge Part III formalization, hand-written, classical extremal combinatorics.
- Tao 2026: Claude Code + Lean for analysis. Stylistic precedent.
- AlphaProof (Weng et al. 2024) and AlphaGeometry (Trinh et al. 2024): DeepMind's RL+Lean for IMO; different scale.
- Polu & Sutskever 2020 (GPT-f); Jiang+ 2022 (Thor); First+ 2023 (Baldur); Song+ 2024 (Lean Copilot).

### 9. Conclusion + future work (0.5 page)
- The 5/10 calibration + Round E result demonstrates the pipeline is **research-grade for extremal combinatorics**.
- Future targets: push to 8/10 calibration (C3, C6, C4 general, C10); attempt P(Hasse connected) at N=7 as a second open-problem extension; contribute random-poset infrastructure to Mathlib.
- Open question: closed-form formula for E[|Aut|] at general N.

## Companion artifacts
- Public Lean repo: github.com/MattLoftus/automath (this paper documents the state at commit `1c8b95f`).
- Reproducibility: `experiments/` directory with per-theorem notes, Python verification scripts.
- Bibliography from `papers/novelty_check.md`.

## Drafting plan
- Session 7: write Sections 1, 2, 3 (intro, pipeline, calibration substrate).
- Session 8: write Sections 4, 5 (calibration results + methodology).
- Session 9: write Sections 6, 7, 8 (Round E, limitations, related work).
- Session 10: cold-read score check via subagent (per CLAUDE.md), revise.
- Session 11: arXiv submission.

Estimated total: ~5 sessions (10–15 hours).

## Companion combinatorics paper

If Round E expands to N=7 and a recurrence is identified, draft a separate combinatorics paper (3–5 pages) at J. Combin. Theory A or Random Structures & Algorithms:

**Title:** "Expected automorphism group size for random 2-orders: exact values and a recurrence"

Content:
- Definition: E[|Aut|] for random 2-orders on Fin N.
- Theorem: exact values for N=2..7 (or N=8 if computed).
- Conjecture/Theorem: closed-form / recurrence (if found).
- Connection to A001035 and dimension-2 vs dimension-≥3 partition.
- All verified by enumeration (Python script in supplemental).

If no recurrence: still publishable as a sequence-extension note in a more specialized venue (Discrete Math?) — though scoring drops to 6.0–6.5 per RESEARCH_LEARNINGS lesson 97 (characterization caps).
