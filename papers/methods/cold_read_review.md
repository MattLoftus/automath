# Cold-read peer review of the methods paper draft

**Date:** 2026-04-29
**Reviewer:** Independent subagent with no conversation context, given only the .tex file and the CLAUDE.md scoring rubric.
**Score:** **5.0**

This score is the official paper score per CLAUDE.md ("Cold-read mandatory before final scoring"). My pre-cold-read estimate of 7.0–7.5 was inflated by ~2 points — RESEARCH_LEARNINGS lesson 41 (sub-result accumulation) and lesson 41 audience-bound ceiling in action.

## Summary of the review

**Strengths flagged:**
- Honest framing throughout (kernel vs. external trade-offs documented).
- Catalog of recurring Lean tactical pitfalls (Sec 4.2) is useful practitioner knowledge.
- Counting-form vs. probability-form methodology insight is well-reasoned.
- OEIS A001035 cross-check provides independent validation.

**Weaknesses flagged:**
1. **The 65% vs. 7% comparison is misleading.** CombiBench measures whole-problem solve rate on contest math; ours measures sub-lemma first-try on identities pre-proved by hand. Acknowledged in paper but still featured prominently.
2. **N=5 calibration sample is small** and several proofs reuse the same `permLtCount` machinery (not independent).
3. **Open-problem extension is computational**, not LLM-driven. The 132-line Python script could be written by any combinatorialist; the "research-grade" framing oversells.
4. **The Θ(log N) conjecture is unsupported** by 6 data points.
5. **N=6,7 are axioms, not theorems.**
6. **Venue is unclear** — methods paper plus combinatorics result, neither strong enough alone.
7. **Workflow novelty is limited** — "no-API, grep-only" is a configuration choice over Tao's published practice.

## Score-improving revisions (per the cold-read reviewer)

| Action | Effort | Score impact |
|--------|--------|--------------|
| Complete 8/10 calibration with independent (non-machinery-reusing) proofs | ~3 sessions | 5.0 → 5.5–6.0 |
| Run pipeline on held-out CombiBench problems for apples-to-apples comparison | ~2 sessions | 5.5 → 6.0–6.5 |
| Replace N=6 axioms with kernel-checked proofs via packed-array Lean encoding | ~2-3 sessions | 6.5 → 6.5–7.0 |

To reach 7.0+ requires **all three**, totaling ~7-8 more sessions.

## Decision implications

Per CLAUDE.md scoring rubric:
- **Score 5.0:** Publishable in a specialist journal (CQG, J. Combin. Theory). Real contribution but specialist audience only.
- Score 6.0+: requires the revisions above.

The honest landing zone for the project as currently scoped is **5.0–5.5** for the methods paper. The Round E new exact values (E[|Aut(P_6)|] = 349/80, E[|Aut(P_7)|] = 3479/720) could be a separate combinatorics-paper note — the cold-read reviewer didn't separately score that, but it's likely 5.0–6.0 standalone (a sequence extension at two new values, no closed form).

## What I'd do differently

1. **Score honestly the first time.** I was at 7.0–7.5 in my self-estimate; the cold read came in at 5.0. The 2-point gap is exactly the inflation lesson 41 warns about.
2. **Avoid the 65% vs. 7% framing.** It's apples-to-oranges and a sharp reviewer will flag it (and did).
3. **Drop unsupported conjectures.** The Θ(log N) one weakens the paper.
4. **Don't claim "research-grade" for what is fundamentally an enumeration script.**

## Status

The 5.0 score is what gets recorded in trackers. To improve it requires the three revisions above (~7-8 sessions of additional work). Without those, the methods paper lands at 5.0 and the combinatorics paper standalone lands at 5.0–6.0.
