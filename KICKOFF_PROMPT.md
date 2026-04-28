# AutoMath — Kickoff Prompt

*Paste the content below into a new Claude Code chat to begin this project.*

---

## [Begin paste into new chat]

I'm starting a new research project: **a Claude-driven agent pipeline that proposes mathematical conjectures + formalizes proofs in Lean 4 with Mathlib4, calibrated on my published QG Paper G identities in extremal combinatorics.** The project is fully scoped in `~/workspace/automath/PLAYBOOK.md`. Please read that file in full before doing anything else.

Also read, in this order:
1. `~/SOUL.md` — my ethos
2. `~/CLAUDE.md` — project defaults, scoring rubric, upkeep rules
3. `~/.claude/projects/-Users-Loftus/memory/MEMORY.md` — persistent memory
4. `~/workspace/RESEARCH_LEARNINGS.md` — 90+ cross-project lessons. **Pay special attention to lessons on theorems-beat-numerics (the whole rationale for this project), calibration-before-exploration (hard gate in Week 1), and score inflation (cold-read subagent mandatory).**
5. `~/workspace/quantum-gravity/papers/exact-combinatorics/` — my QG Paper G, which contains the 15+ theorems that are this project's calibration substrate. Skim the theorem statements.
6. `~/workspace/automath/PLAYBOOK.md` — this project's full plan

## The thesis in one sentence

Build a Claude + Lean 4 + Mathlib pipeline that auto-formalizes my published QG Paper G theorems (E[link]=N(N−1)/4, E[f]=1/2, E[maximal]=H_N, P(dim=2)=1−1/N!, etc.) with rigorous per-step verification rate measurement, as a calibrated methodology for LLM-driven formalization in extremal combinatorics — and, if calibration passes, push to one new open-problem extension (e.g., exact P(Hasse connected) at N=7 or E[|Aut|] at N=6).

## Today's goals (first session, 2-4 hours)

**This project has the steepest learning curve of any in my portfolio. Session 1 is mostly orientation and tutorial work.**

1. **Orient** — read all files listed above. Skim QG Paper G theorem statements (the calibration targets).
2. **Install elan + Lean 4** (per PLAYBOOK §17):
   ```
   curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
   source $HOME/.elan/env
   ```
3. **Install VS Code Lean 4 extension** — extension ID `leanprover.lean4`.
4. **Begin "Theorem Proving in Lean 4" tutorial** — chapters 1-3. This is the real investment. Budget 90-120 minutes.
5. **Write `HelloMath.lean`** — `theorem hello : 1 + 1 = 2 := by rfl`. Compile with `lean HelloMath.lean`. Commit.
6. **Skim Mathlib4 combinatorics** — `git clone https://github.com/leanprover-community/mathlib4` and browse `Mathlib/Combinatorics/`. Note coverage of posets, orders, random structures.
7. **Log** — `experiments/exp00_lean_setup/notes.md`.

Do **not** in Session 1: attempt Claude+Lean pipeline work, attempt QG Paper G theorems, design the Mathlib RAG system.

## The critical Week 1 gate

By end of Week 1 (not Session 1), I must be able to **hand-formalize** QG Paper G's simplest theorem — `theorem elink : ∀ N, E[link_count N] = N*(N-1)/4` — in Lean 4 by hand. This is a 2-line proof if the random-order infrastructure exists in Mathlib, or a 20-line proof if I have to build it myself.

**If I can't pass this gate by Day 14, pause the project.** The pipeline work downstream requires me to be able to read Lean fluently enough to debug what Claude produces. Without that, the project is hopelessly outsourced to a black box.

This gate is my defense against spending weeks on a project that requires capabilities I don't have yet.

## Critical standards I expect you to follow

- **This is a project where the learning curve IS the first milestone.** Don't let me skip tutorial work to rush to the "interesting" pipeline code. The pipeline is worthless if I can't read the output.
- **Novelty check mandatory at Week 2.** DeepMind AlphaProof, Terence Tao's Lean+Claude work, OpenAI internal efforts — big labs are in this space. Our angle is: independent lab + extremal combinatorics domain + Claude-specific. Verify this angle is still novel before scaling.
- **Calibrate before exploring.** Week 1 hand-formalization is the calibration. Week 2 pipeline on C1 (trivial theorem) is second calibration. Don't attempt novel results before both pass.
- **Nice every CPU-heavy command.** Mathlib's build cache is large. Embedding index generation over Mathlib is substantial. `nice -n 10`.
- **Cost awareness.** Claude API budget: ~$200-500/mo expected. Use Haiku for simple classification / error parsing, Sonnet/Opus for proof planning. Track spend.
- **Score honestly.** A negative methods paper ("here's why this pipeline is bounded") is still 6.0-6.5 and publishable. Don't inflate.
- **Cold-read scoring.** Any paper claim ≥ 7.5 gets a subagent cold-read per CLAUDE.md.
- **Theorem-first framing.** The valuable output is a theorem proved + verified, not "Claude generated something that looked right." The Lean compiler is the adjudicator.

## Environment quick-reference (from MEMORY.md)

- System Python: `/usr/bin/python3` (3.9.6). Do not use Anaconda.
- LaTeX: `tectonic`.
- GitHub CLI: `gh` authenticated as MattLoftus.
- Project root: `~/workspace/automath/`
- QG Paper G location: `~/workspace/quantum-gravity/papers/exact-combinatorics/`
- Claude API: I have working API patterns in other projects if needed — check `~/workspace/niche-sites/` or `~/workspace/stock-picks/` for Anthropic SDK usage examples.

## Blockers to know about

- **arXiv `cs.LO` endorsement.** I don't have this. `math.CO` also not. Submission plan: either find a Lean-community endorser (Kevin Buzzard?) or lead with `stat.ML` (which I have via Mahoney) framed as an ML paper about formalization.
- **Mathlib coverage for random orders / poset probability is sparse.** Expect to write small Mathlib contributions as part of the project. That's fine — community contribution is a bonus, not a blocker.
- **100GB+ disk for Mathlib build cache.** M4 Pro 1TB is fine; just budget it.

## Questions I expect you to ask me (before coding)

1. Am I emotionally prepared for a 2-week Lean 4 learning curve before the "interesting" Claude work starts? (Honest answer if no: scope-narrow or pivot.)
2. arXiv venue: `cs.LO` or `stat.ML` lead? I lean `stat.ML` (Mahoney-endorsed, avoids endorsement block) with `cs.LO` + `math.CO` cross-list.
3. Claude API budget for this project? I'm willing to spend ~$500/mo if the pipeline shows promise. But if it doesn't, I want to cap at $100/mo until it does.
4. Public GitHub repo from day 1 (Lean community norm) or wait?
5. Do I want to pair with Terence Tao's Lean workflow blog posts as a stylistic anchor? (He's the most public academic doing this.)

## When you're done with Session 1, report back

- Whether elan + Lean 4 installed cleanly
- Whether VS Code Lean extension works
- How far into "Theorem Proving in Lean 4" you got with me
- `HelloMath.lean` compile result
- Quick assessment of Mathlib4 combinatorics coverage — does it have `Combinatorics.Poset` or similar at a useful level?
- Honest assessment of Lean learning curve for me given what I've read
- Plan for Session 2

If the honest assessment of the learning curve is "Matt needs 3+ weeks of dedicated tutorial work before even attempting the pipeline," tell me that — I want honesty over optimism. I'd rather scope-narrow or pause the project than limp forward.

## [End paste into new chat]

---

## Notes for Matt (not part of the prompt)

- This is the most ambitious fresh pick in V4, and it has the highest learning-curve risk. The Week-1 hand-formalization gate is the whole point — if you can't write a 2-line Lean proof by hand after 1 week of tutorials, the pipeline work is out of reach for now.
- Terence Tao is your nearest public peer in this workflow. His blog posts on using Claude + Lean for polynomial method proofs are the closest thing to a template for what we're doing.
- The methods paper ("we built a pipeline, here's what it can and can't do") is the floor. The new-result paper ("we discovered X via the pipeline") is the ceiling. Both are worth aiming for.
- If calibration fails hard (< 3 of 10 theorems pass), consider pivoting to a simpler domain: Stirling-number identities, integer-partition generating functions. Those have much better Mathlib coverage.
- Budget time for the Mathlib learning curve independently of the Claude work. The two are separable skills.
- Consider this project the "ambitious bet" in a portfolio that includes SpectraLens (safe ship) and LIGO (research extension). Don't feel bad if this one takes longer or fails — it's the 9+ upside pick.
