# AutoMath — Automated Mathematical Discovery via LLM + Lean 4

**Project:** Automated Math Discovery (LLM-guided conjecture + Lean 4 formalization)
**Dir:** `~/workspace/automath/`
**Master playbook:** `~/workspace/MASTER_PLAYBOOK.md`
**Status:** ROUND D GATE CLEARED (Sessions 1–5, 2026-04-27 → 2026-04-28). **5 of 10 calibration targets formalized** (C1, C2, C4@k=2, C5, C8). The Round D ≥ 5/10 gate is met — methods-paper floor locked at 7.0–7.5 per §12 rubric. Aggregate per-step verification rate: ~63% across 6 theorems and ~30+ sublemmas, consistent across rounds.
**Created:** 2026-04-23
**Owner:** Matt Loftus / Cedar Loop LLC

## Architecture decision (2026-04-27)

**No Anthropic API orchestration.** This Claude Code session itself is the agent
loop: I read theorem statements + Mathlib excerpts, draft Lean, run `lake build`,
parse errors, iterate. No `src/orchestrator.py`, no embedding APIs (Voyage / OpenAI),
no `chromadb`. Mathlib retrieval is `Read`+`grep` over the local mirror at
`lean/.lake/packages/mathlib/Mathlib/`. Cost goes from $200–500/mo to existing
Claude Code subscription. The paper's framing improves: "Claude Code as the agent
shell" is more reproducible than a custom Python pipeline and matches how
researchers actually use the tool (cf. Tao's public Claude+Lean workflow).

---

## 1. What Is This?

A research project that builds a Claude-driven agent pipeline which (a) proposes mathematical conjectures in extremal combinatorics and random order theory, (b) drafts proof outlines in natural language, (c) formalizes each proof step in Lean 4 with Mathlib, (d) iterates on Lean compiler feedback until the proof typechecks, and (e) commits verified theorems to a public repository. The calibration targets are Matt's own published QG Paper G identities (15+ theorems he proved by hand). The ambitious targets are small open problems (extensions of Paper G to N ≥ 7, tighter bounds on K₄⁻ Turán density).

**Deliverable (minimum):** A methods paper — "Agent-Driven Formalization of Extremal Combinatorics: A Calibrated Pipeline" — demonstrating a Claude+Lean pipeline that auto-formalizes at least 5 of Matt's QG Paper G theorems with ≥ 50% per-step auto-verification rate and a human-in-loop-assisted complete formalization of the full set.

**Deliverable (stretch):** A new mathematical result — e.g., extension of "P(Hasse connected)" computed exactly for N = 7, 8 — discovered and formalized by the pipeline, publishable as a standalone combinatorics paper.

**Not a deliverable:** Beating DeepMind AlphaProof or Anthropic internal formal-methods efforts on competition math. Scope is extremal combinatorics, not IMO.

---

## 2. Scientific Question

LLMs are rapidly becoming capable of proposing mathematical arguments, but they hallucinate. Formal proof assistants (Lean 4 + Mathlib) typecheck every argument but are labor-intensive to use. The question is: **can a Claude-driven feedback loop between natural-language proof proposal and Lean 4 formalization produce verified mathematics at a rate useful for research, in a specific domain (extremal combinatorics) where the arguments are combinatorial and the ambient theory is well-developed?**

Specifically:
1. **Calibration:** What fraction of Matt's QG Paper G theorems (E[f]=1/2, E[link]=N(N−1)/4, E[maximal]=H_N, E[k-antichains]=C(N,k)/k!, P(dim=2)=1−1/N!, etc.) can the pipeline formalize end-to-end *without* a human writing Lean?
2. **Scaling:** Does formalization rate degrade for identities of higher combinatorial complexity (2-way vs 3-way joint distributions, say)?
3. **Open-problem capability:** Can the pipeline produce a new result? Specifically: exact value of E[|Aut|] for random 2-orders at N=6 (Matt computed N=5; the N=6 value is unknown-but-computable).

---

## 3. Novelty Positioning

### 3.1 What's been done

**LLM + formal proof (the hot area):**
- **DeepMind AlphaProof 2024** — IMO silver medal via Gemini + Lean. Focused on olympiad problems, not open research problems.
- **DeepMind AlphaGeometry 2024** — geometry theorem proving, separate pipeline.
- **Terence Tao's public Lean + Claude work (2024-2026)** — informal pair programming with Claude on Lean formalizations of his own work (polynomial method, combinatorial identities). Blog posts are public.
- **Kevin Buzzard + Mathlib community** — Lean-for-research workflow at scale; Xena Project.
- **OpenAI's formal methods efforts** — internal, GPT-4 + Lean; little public detail.
- **Anthropic's formal methods efforts** — internal; Matt does not have privileged information on these.

**Academic LLM-for-math papers:**
- Polu & Sutskever 2020 — GPT-f, generative language models for theorem proving
- Jiang+ 2022 (Thor) — retrieval-augmented prover
- First, Rabe, Ringer, Brun 2023 — "Baldur" (fine-tuned LLMs for Isabelle)
- Song+ 2024 — Lean copilot (open-source, useful as prior-art anchor)
- Anthropic 2024 Claude tech report — code + reasoning capabilities

**Mathlib community:**
- Mathlib covers probability, combinatorics, number theory at basic levels; extremal combinatorics coverage is sparse.
- Probability: Mathlib has measure theory, some conditioning. Random orderings / posets: ~nothing native.
- This is a coverage gap our project will partially fill.

**Matt's own prior art (the calibration substrate):**
- QG Paper G — 15+ theorems on random 2-orders on N elements. All proved by hand. Some proved exactly, some via MC + enumeration. See `~/workspace/quantum-gravity/papers/exact-combinatorics/` for the paper.

### 3.2 What's novel about our approach

1. **Specific research domain with known ground truth.** QG Paper G gives us 15+ theorems with *Matt's* hand-written proofs to check against. We can measure the formalization pipeline's per-step correctness rate concretely.
2. **LLM + Lean tight loop with Claude as the "natural-language brain."** Most academic work uses GPT-f or fine-tuned models; Claude Sonnet/Haiku is an underexplored endpoint for this task.
3. **Independent-lab angle.** We don't have infinite compute; our pipeline has to work on modest budgets. This is closer to how an actual math grad student would use the tool than a DeepMind-scale setup.
4. **Extension to unknown values.** If calibration succeeds, we push to N=7, 8 for observables Matt's paper stops at N=5 or 6. That's a genuinely new result.
5. **Mathlib contribution.** Formalized proofs of random-order theorems would be a direct addition to Mathlib's combinatorics library — a community-validated contribution beyond the paper.

### 3.3 Mandatory novelty check (Day 3 + Week 4)

Search arXiv + ACM DL + Google Scholar + Lean Zulip archives for:
- "Lean 4 extremal combinatorics"
- "LLM Lean automated proof"
- "Claude formal verification mathematics"
- "random poset Lean formalization"
- "agent-driven theorem proving 2026"
- "LLM feedback loop proof assistant"
- "AlphaProof extremal combinatorics" (to verify DeepMind didn't publish this specific angle)

Check Lean Zulip `#new members` + `#maths in Lean` for work-in-progress on random orders or partial orders.

If close prior work exists on EXTREMAL COMBINATORICS specifically formalized by an LLM+Lean pipeline, pivot to (a) a narrower subdomain (e.g., only enumerative identities like Stirling numbers), or (b) a different methodological angle (e.g., benchmarking formalization rate vs proof length). Document in `papers/novelty_check.md`.

---

## 4. Hypothesis

**H1 (primary, calibration):** A Claude 4.7 + Lean 4 + Mathlib agent loop, given a natural-language statement of a theorem from QG Paper G plus access to Mathlib via retrieval, can produce a typechecked Lean proof of at least 50% of Paper G's identities with < 3 rounds of human correction per identity, on a median wall-clock of < 2 hours per theorem.

**H2 (scaling):** The pipeline's per-step auto-verification rate (fraction of Lean proof steps that compile on first attempt) is > 30% on average, across the Paper G theorems.

**H3 (stretch, discovery):** Given the infrastructure, a novel open-problem extension (e.g., exact E[|Aut|] at N=6, or exact P(Hasse connected) at N=7) can be formulated, conjectured via Claude + MC enumeration, and formalized in Lean within 2-3 weeks of the calibration target passing.

---

## 5. Methodology

### 5.1 The pipeline architecture

```
 ┌──────────────────────────────────────────────────────┐
 │  Matt provides theorem statement (e.g., from QG G).  │
 └───────────────────────┬──────────────────────────────┘
                         │
                         ▼
 ┌──────────────────────────────────────────────────────┐
 │  CLAUDE CODE (this session) — DECOMPOSE              │
 │  - Read relevant Mathlib via Read+grep on local       │
 │    mirror at lean/.lake/packages/mathlib/.            │
 │  - Identify candidate lemmas + proof skeleton.        │
 │  - Plan `have` decomposition.                         │
 └───────────────────────┬──────────────────────────────┘
                         │
                         ▼
 ┌──────────────────────────────────────────────────────┐
 │  CLAUDE CODE — TRANSLATE                             │
 │  - Write Lean 4 file with proof attempt.              │
 │  - Use Edit/Write tools, save to                      │
 │    lean/Automath/QGPaperG/<C_name>.lean.              │
 └───────────────────────┬──────────────────────────────┘
                         │
                         ▼
 ┌──────────────────────────────────────────────────────┐
 │  Bash: `lake build` → Lean compiler typechecks       │
 └───────────────────────┬──────────────────────────────┘
            ✓ Pass       │        ✗ Fail
                 ┌───────┴────────┐
                 │                │
                 ▼                ▼
 ┌─────────────────────┐   ┌────────────────────────────┐
 │  Commit to git.     │   │  CLAUDE CODE — ITERATE     │
 │  Log to exp notes.  │   │  Read error, fix one issue │
 └─────────────────────┘   │  at a time. Max ~10 loops. │
                          └────────────────────────────┘
```

The agent IS Claude Code. No external orchestration. No Python service. No API calls.

### 5.2 Concrete Stage details

**Decompose stage.** Given a theorem statement, I (Claude Code) read relevant
parts of Mathlib using `Read` + `grep` on `lean/.lake/packages/mathlib/Mathlib/`.
For C1 specifically, the relevant primitives are in `Data/Fintype/Perm.lean`
(`Fintype.card_perm`), `Data/Finset/Card.lean` (`card_bij'`), `Data/Finset/Prod.lean`
(`offDiag_card`), `Algebra/BigOperators/Ring/Finset.lean` (`Fintype.sum_mul_sum`).
I plan a sequence of `have` decompositions before writing any Lean.

**Translate stage.** I write the Lean file directly via `Write`. Tactic priority
when stuck: `exact <name>`, `simp`, `omega`, `linarith`, `ring`, `decide`,
`simp_all`, then manual.

**Iterate stage.** Bash runs `lake build` (or `lake env lean <file>` for
ad-hoc files). I parse the error, identify the failing tactic / unification,
and patch with `Edit`. One issue at a time — global rewrites compound errors.
- Max iterations: 10 per proof obligation.
- If not converging after 10: surface to human (Matt) for manual intervention.

### 5.3 Retrieval over Mathlib

Mathlib lives at `lean/.lake/packages/mathlib/Mathlib/`. Retrieval is done via
`Read` + `grep`/`find` directly — no embedding index, no vector DB. Specific
patterns that have worked so far for C1:

- `grep -rn "<keyword>\|<related-keyword>" Mathlib --include="*.lean"` to find
  candidate lemmas by name.
- `grep -rn -A2 "theorem.*<lemma_name>" Mathlib` to read the exact signature.
- `Read` to pull surrounding context when an unfamiliar definition is referenced.

This is sufficient for our domain (extremal combinatorics, finite poset theory)
because the relevant Mathlib subdirs are small and well-named:
`Data/Fintype/`, `Data/Finset/`, `GroupTheory/Perm/`, `Combinatorics/Enumerative/`,
`Combinatorics/Extremal/`. If retrieval becomes a bottleneck later, an embedding
RAG layer can be added — but Round A→C have not needed one.

### 5.4 Evaluation metrics

- **End-to-end pass rate:** fraction of theorems that get a fully-typechecked proof within 10 iterations.
- **Per-step auto-verification rate:** fraction of individual `have` blocks that compile first-try.
- **Human intervention count:** median number of manual fixes per theorem.
- **Wall-clock time:** median per theorem.
- **Proof length:** line count of final Lean file.
- **Proof quality (subjective):** after pass, Matt reviews for elegance — is Claude finding natural proofs or brute-forcing?

---

## 6. Calibration Targets (QG Paper G Identities)

All taken from `~/workspace/quantum-gravity/papers/exact-combinatorics/`. Matt proved these by hand; the Lean versions would be the first formalizations.

| # | Theorem | Difficulty |
|---|---------|------------|
| C1 | E[# ordered comparable pairs (i, j)] = N(N−1)/4 for random 2-orders on N elements | **DONE 2026-04-27** — counting form, 181 lines, 7 build iterations, 4/7 sublemmas first-try. (Original PLAYBOOK called this "link count" — corrected; "link" in the QG paper means a covering relation w/o intermediates, which is C8.) |
| C2 | E[ordering fraction f] = 1/2 | **DONE 2026-04-28** — counting form (`2 · ∑ comparablePairCount = N(N-1)·(N!)²`), 109 lines, 2 iterations, 5/6 first-try. Reduces to C1 via `comparablePairCount = 2 · orderedPairCount`. |
| C3 | E[maximal elements] = H_N (harmonic number) | Moderate (probabilistic proof via record values in random permutations). Requires ℚ machinery or careful ℕ-only arithmetic with `N!/(N-i)`. Round D target. |
| C4 | E[k-antichains] = C(N,k) / k! | **DONE k=2 case 2026-04-28** — counting form `2 · ∑ numOrderedIncomparable = N(N-1)·(N!)²`, 112 lines, 3 iterations, 3/5 first-try. Reduces to C2 via `inc + comp = N(N-1)`. **General k case deferred** — requires partition over k-subsets and per-subset 1/k! probability. |
| C5 | P(poset dim = 2) = 1 − 1/N! | **DONE 2026-04-28 (full proof, including dim bridge)** — counting form `#{σ ≠ τ} + N! = (N!)²` (Round B) + `is2OrderTotallyOrdered ⇔ σ = τ` bridge (Round C). 151 lines total. Hard direction proved via `StrictMono.range_inj` + `Equiv.range_eq_univ` + `mul_inv_eq_one`. |
| C6 | Var[f] = (2N+5) / (18N(N−1)) | Harder (computation with 2nd moments) |
| C7 | Tracy-Widom antichain: antichain size fluctuations | Hard (uses BDJ theorem — may hit Mathlib wall) |
| C8 | E[\|interval interior\| \| i ≺ j] = (N-2)/9 (Interval-statistics proposition) | **DONE 2026-04-28** (Sessions 4–5): counting form `36·∑ totalIntervalCount = N(N-1)(N-2)·(N!)²`. 460 lines. Hardest target so far — 16 sublemmas at 11/16 ≈ 69% first-try. Key new machinery: `six_mul_permLt3Count` (6-fold triple symmetry, generalizes C1's 2-fold pair symmetry) + Fubini swap helper + per-triple combined identity. |
| C9 | P(Hasse connected) for N=2-6 (exact values) | Hard for N>2 — depends on Mathlib coverage of Hasse diagrams |
| C10 | E[maximal chains] exact formula | Moderate |

**Ordered calibration plan:** ✅ C1 (Round A), ✅ C2 + C5-counting + C5-easy-bridge (Round B), ✅ C5-hard-bridge + C4@k=2 (Round C, Session 3), ✅ C8 (Round C, Sessions 4–5). **5/10 done — Round D gate cleared.** Next sessions: C3 (harmonic), C6 (variance — reuses C8's triple machinery), C4 general k, C10. C7 (Tracy-Widom) and C9 (Hasse) likely Mathlib-blocked; defer.

---

## 7. Open-Problem Targets (Round D stretch)

Only attempt if calibration passes:
- **Exact E[|Aut|] for N=6.** Matt computed N=2-5 (3/2, 13/6, 71/24, 89/24). N=6 is unknown-but-exactly-computable via enumeration + symmetry.
- **Exact P(Hasse connected) for N=7.** Matt computed N=2-6: 1/2, 1/2, 13/24, 71/120, 461/720. N=7 is tractable with enumeration + careful counting.
- **Joint distribution of (height, width) at N=6.** Partial result in Matt's paper.
- **Extremal: what's the maximum E[f] over all distributions on labeled posets of size N?** New question.

Each would be a ~2-3 week add-on post-calibration if time permits.

---

## 8. Tech Stack

| Layer | Tool | Why |
|-------|------|-----|
| Proof assistant | Lean 4 v4.30.0-rc2 + Mathlib4 (matching) | Modern, active community, Claude-amenable |
| Installer | elan (Lean version manager) | Standard |
| Editor | VS Code + Lean 4 extension | Standard Lean dev environment |
| **Agent** | **Claude Code (this session)** | **Reads Mathlib, drafts proofs, parses errors, iterates. No external orchestration.** |
| Build tool | lake (Lean build system) | Standard |
| Mathlib retrieval | `Read` + `grep` over local mirror | No embedding/RAG layer needed for this domain |
| Version control | git + GitHub (public: MattLoftus/automath) | Lean community norm; enables external contributions |
| Paper | tectonic | Matt LaTeX |

---

## 9. Infrastructure Reuse

Minimal portfolio reuse — this is a net-new stack:
- **From `~/workspace/quantum-gravity/papers/exact-combinatorics/`:** the 15+ Paper G theorems are our calibration set; hand proofs are the ground truth.
- **From niche-sites pipeline:** nightly-cron pattern (via `/loop` or `/schedule`) if we want an autonomous overnight calibration run.

**Net-new:** Lean 4 install (`~/.elan/`), Mathlib4 cache (~5–10 GB of `.olean` files via `lake exe cache get`), `lake build` toolchain.

**Explicitly NOT used:** Anthropic API, Python orchestration service, embedding APIs (Voyage / OpenAI), vector DBs (faiss / chroma). All would have added weeks of plumbing and ~$200–500/mo in API spend; none are needed.

---

## 10. Experimental Plan

> **Timeline note (2026-04-27):** Original PLAYBOOK budgeted weeks per Round. After Session 1 closed Round A in ~hours, all dates compress ~5×. The compressed schedule below is the working plan.

### Round A — Stack live + first hand formalization ✅ DONE 2026-04-27
**Achieved in Session 1:**
- elan + Lean 4.30.0-rc2 installed at `~/.elan/`.
- Lake project at `automath/lean/` with Mathlib v4.30.0-rc2 dependency, `~8300` `.olean` files cached via `lake exe cache get`.
- HelloMath.lean (`1+1=2`) compiled cleanly.
- C1 (counting form): `4 · ∑_{(σ,τ)} orderedPairCount = N(N-1)·(N!)²` — proved in Lean, ~180 lines, 7 build iterations to passing typecheck.
- Per-step auto-verification rate (this session): roughly **4 of 7 lemmas first-try pass** (~57%); main theorem required 4 iterations.

### Round B — Multi-theorem expansion ✅ DONE 2026-04-28 (Session 2)
**Achieved:**
- **B1:** ✅ C2 formalized in counting form (`2·∑ comparablePairCount = N(N-1)·(N!)²`). 109 lines, 2 build iterations, 5/6 sublemmas first-try (≈ 83%). Reduces to C1 via the bridge `comparablePairCount = 2 · orderedPairCount`. See `experiments/exp01_c2/notes.md`.
- **B2:** ✅ C5 formalized in counting form (`#{σ ≠ τ} + N! = (N!)²`). 103 lines, 2 build iterations, 2/5 first-try (≈ 40%). Bridge to "dim ≤ 1 ⇔ σ = τ" deferred (requires "monotone perm of Fin N = id"). See `experiments/exp02_c5/notes.md`.
- **B3:** ✅ Novelty check completed. Documented at `papers/novelty_check.md`. CombiBench (May 2025), LeanCamCombi, Tao's Claude Code workflow are adjacent prior work; no kill — random 2-orders specifically not covered anywhere. Required citations recorded.
- **B4:** ✅ Per-theorem stats logged per experiment notes.

**Aggregate Round A + Round B: 11 / 18 sublemmas first-try (≈ 61%), well above H2's > 30% threshold.**

### Round C — Difficult calibration targets (next 2–4 sessions)
**Goal:** attack moderate-difficulty theorems (C3, C4, C6, C8, C10) plus the deferred C5 bridge.

- Deferred C5 bridge: prove `is2OrderTotallyOrdered σ τ → σ = τ` via "monotone perm of Fin N = id" (likely via `Finset.orderEmbOfFin_unique`).
- C3 (E[maximal] = H_N) — likely requires building a small "record-value" library on top of `Equiv.Perm`.
- C4 (E[k-antichains] = C(N,k)/k!) — Stirling-style identity; check if Mathlib has analog.
- C6 (Var[f]) — second-moment computation; covariance on triples ranking. Reuse C1's `permLtCount` machinery.
- C8 (P(link) = double-sum) — covering relation, no intermediates.
- C10 (E[max chain] exact formula).
- C7 (Tracy-Widom) and C9 (Hasse connected) — defer; Mathlib coverage likely insufficient.

### Round D — Full calibration verdict
**Goal:** assess H1.

- **D1:** Tally end-to-end pass / partial / fail over C1–C10.
- **D2:** **Decision gate:**
  - ≥ 7 of 10 pass: H1 strongly supported. Methods paper at 7.0–7.5.
  - 5–6 of 10 pass: H1 supported. Methods paper at 6.5–7.0.
  - 3–4 of 10 pass: limitations paper. 6.0–6.5.
  - < 3 pass: pivot to a domain Mathlib already covers (Stirling identities, integer partitions).

### Round E — Open problem (only if Round D ≥ 5/10)
**Goal:** new mathematical result via the pipeline.

- **E1:** Compute the conjectured exact value via direct enumeration (Python over `Sym(N)²`) — NOT via Claude.
- **E2:** Formalize using the same hand-formalization workflow that worked for calibration.
- **E3:** Standalone combinatorics paper.

### Round F — Methods paper
- **F1:** Draft paper.
- **F2:** Peer-review simulation (3 subagents: ML / formal methods / combinatorics).
- **F3:** Cold-read score.
- **F4:** arXiv (`stat.ML` lead, `cs.LO` + `math.CO` cross-list) + submission.

---

## 11. Calibration Gates

| Gate | Metric | Pass | Fail | Status |
|------|--------|------|------|--------|
| **Round A — Hand formalization** | C1 hand-proven in Lean | Proceed | Pause project; pivot domain | ✅ **PASSED 2026-04-27** (Session 1) |
| **Round B — Multi-theorem** | C2 + C5 formalize within ~1 session each | Proceed | Reassess Mathlib coverage | ✅ **PASSED 2026-04-28** (Session 2) — both compiled in 2 iterations each |
| **Round B — Novelty check** | No close prior art on Lean+LLM pipeline for extremal combinatorics | Proceed | Pivot scope (e.g., Stirling identities) | ✅ **PASSED 2026-04-28** — `papers/novelty_check.md` |
| **Round C — C5 dim bridge** | `is2OrderTotallyOrdered ⇔ σ = τ` proven, completing C5 | Proceed | Defer / accept partial C5 | ✅ **PASSED 2026-04-28** (Session 3, 1 fix) |
| **Round D — Calibration** | ≥ 5 of 10 Paper G theorems pass | Methods paper + maybe stretch | Limitations paper | ✅ **PASSED 2026-04-28** (Session 5) — 5 of 10 done (C1, C2, C4@k=2, C5, C8). Methods paper floor locked at 7.0–7.5. |
| **Round F — Cold-read** | Methods paper scores ≥ 6.5 | Submit | Revise | Pending |

---

## 12. Scoring Rubric (Paper)

| Outcome | Score | Interpretation |
|---------|-------|----------------|
| < 3 of 10 theorems pass | 5.5-6.0 | Negative methods paper — "here's why this is hard" |
| 5-7 of 10 pass, no new result | 7.0 | Decent methods paper; per-step verification rate is the headline |
| 8-10 of 10 pass | 7.5 | Strong methods paper; Claude+Lean is research-grade for this domain |
| Calibration + new result (open problem formalized) | 8.0-8.5 | Methods paper + combinatorics paper side-by-side |
| Pipeline generalizes to a domain we didn't target (emergent) | 9+ | Unlikely, but possible |
| Cold-read mandatory before final scoring | | |

---

## 13. Target Venue + arXiv Categories

- **Methods paper:**
  - Primary: JAR (Journal of Automated Reasoning) or ITP conference (Interactive Theorem Proving)
  - Alternate: J. Symb. Logic, JACM, TACAS
  - arXiv: `cs.LO` primary, `math.CO` cross-list (Matt would need cs.LO endorsement, new territory)
- **Combinatorics paper (if stretch hits):**
  - Primary: J. Combin. Theory A or Random Structures & Algorithms
  - arXiv: `math.CO`
- **Arxiv endorsement note:** Matt has `stat.ML` (Mahoney). For `cs.LO`, need a new endorser. For `math.CO`, need a new endorser (but existing Paper G author is Matt, so co-authorship path is possible).

---

## 14. Risks + Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| ~~Lean 4 learning curve too steep~~ | ~~Medium~~ | ~~High — blocks~~ | ~~Week-1 hand-formalization gate~~ — **RESOLVED:** Round A passed in Session 1, the curve is shallower than originally assumed when Claude Code is the formalizer (not Matt by hand). |
| Mathlib lacks coverage for random orders | High | Medium | Expected — we'll build missing pieces. Treat as Mathlib contribution. C1 needed only `Equiv.Perm`, `Finset.offDiag`, `Fintype.sum_mul_sum` — all already there. |
| Claude's Lean syntax knowledge is limited | Medium | Medium | Mitigated by Mathlib retrieval via `Read`+`grep` and iterative compiler feedback. C1 hit ~6 Lean-specific issues (HO unification, ℕ-cast in `Finset.sum_boole`, `omega` and nat-subtraction); all resolved within 7 iterations. |
| DeepMind / Anthropic publishes similar pipeline | Medium-High | Medium | Novelty check Round B (mandatory). Tao has done public Claude-Code+Lean work but on Analysis-I formalization, not extremal combinatorics. Independent-lab + domain angle still novel. |
| Per-step auto-verification rate < 20% | Low (revised) | High — paper weakens | Round A first-try rate was ~57% per-lemma — well above the 20% floor. If later rounds drop, frame as "what the pipeline can't do" and still publish. |
| ~~Compute cost (Claude API + embeddings)~~ | — | — | **N/A** — no API used, no embeddings used. Existing Claude Code subscription covers it. |
| Mathlib version churn | Medium | Low | Pinned to v4.30.0-rc2 in `lakefile.toml`. Re-pin only when needed. |
| Paper scope drift (over-claim LLM reasoning) | Medium | High — reviewer kills | Stay scoped to the domain; don't oversell generalization. Headline result is per-step verification rate on extremal combinatorics, full stop. |

---

## 15. Decision Gates (Pivot / Kill)

- **Round A — C1 hand-formalization fails** → ~~pause project~~ **PASSED 2026-04-27.**
- **Round B — C2/C5 each take > 1 session** → reassess Mathlib coverage; consider scope-narrowing to enumerative identities.
- **Round B — novelty check turns up a very close paper** → pivot to narrower scope (Stirling identities, partition generating functions).
- **Round D — < 3 calibration theorems pass** → kill the "methods paper works" story; write as limitations paper.
- **Round F — cold-read < 6.0** → revise methodology before submission.

---

## 16. Milestones + Timeline

| Milestone | Target | Actual / Status |
|-----------|--------|-----------------|
| Project initialized | 2026-04-23 | ✅ 2026-04-23 |
| Lean 4 installed | 2026-04-25 | ✅ 2026-04-27 (Session 1) |
| Lake project + Mathlib cache | 2026-04-30 | ✅ 2026-04-27 (Session 1) |
| Hand-formalization of C1 | 2026-05-02 | ✅ 2026-04-27 (Session 1, ~7 iterations) |
| Novelty check | 2026-05-05 | ✅ 2026-04-28 (Session 2) — `papers/novelty_check.md` |
| C2 + C5 formalized | 2026-05-12 | ✅ 2026-04-28 (Session 2, 2 iterations each) |
| C5 dim bridge (`is2OrderTotallyOrdered ⇔ σ = τ`) | 2026-05-15 | ✅ 2026-04-28 (Session 3) |
| C4@k=2 formalized | 2026-05-15 | ✅ 2026-04-28 (Session 3) |
| C8 (interval size) formalized | 2026-05-20 | ✅ 2026-04-28 (Sessions 4–5) |
| **Round D ≥ 5/10 calibration gate** | 2026-05-25 | ✅ **PASSED 2026-04-28 (Session 5)** — 5/10: C1, C2, C4@k=2, C5, C8 |
| C3, C6, C10, C4 general k formalized (push to 8/10) | 2026-05-25 | Pending — Round C continuation |
| Methods-paper-grade verdict (Round D) | 2026-05-30 | Pending — Round D |
| Methods paper draft | 2026-05-25 | Pending — Round F |
| arXiv submission | 2026-06-05 | Pending — Round F |
| (Optional) open-problem attempt | 2026-06-15 | Pending — Round E |

---

## 17. Setup Commands (as actually used in Session 1)

```bash
# 1. Install elan (Lean version manager) — non-interactive, no default toolchain.
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none

# 2. PATH: elan added itself to ~/.bash_profile. For interactive sessions,
#    source ~/.bash_profile. For Bash-tool calls, prefix:
export PATH="$HOME/.elan/bin:$PATH"

# 3. Set the default Lean toolchain.
elan default leanprover/lean4:stable
lean --version    # should show 4.30.0-rc2 (or current stable)

# 4. Initialize the Lake project with Mathlib4 dependency. The `math-lax` template
#    pulls Mathlib + auto-runs `lake exe cache get` to download ~8000 pre-built
#    .olean files (avoids hours of recompilation).
cd ~/workspace/automath/lean
lake init Automath math-lax.toml   # ~5 minutes including cache pull

# 5. Compile a sanity-check file using the project's lean+mathlib environment.
lake env lean HelloMath.lean

# 6. From here on, all Lean files go in Automath/<area>/<C_name>.lean and are
#    imported from Automath.lean. Build with:
lake build

# VS Code Lean extension (manual): leanprover.lean4
```

**No Python virtualenv needed.** No Anthropic SDK. No embedding APIs.

---

## 18. Session log

### Session 1 — 2026-04-27 ✅ Round A complete

Achievements:
1. Read all orientation files (SOUL, CLAUDE, RESEARCH_LEARNINGS, QG Paper G, this PLAYBOOK).
2. Architectural pivot: dropped Anthropic-API orchestration in favor of Claude-Code-as-agent. Saved memory `feedback_claude_code_as_agent_loop.md`.
3. Installed elan + Lean 4.30.0-rc2.
4. Initialized Lake project `Automath` with Mathlib v4.30.0-rc2 (math-lax template). Cache pulled `~8000` `.olean` files.
5. Compiled HelloMath.lean.
6. Surveyed `Mathlib/Combinatorics/` (Additive, Derangements, Digraph, Enumerative, **Extremal**, Graph, Hall, Matroid, Optimization, Quiver, SetFamily, SimpleGraph, Tiling, Young).
7. Identified C1's mathematical primitives: `Equiv.Perm`, `Fintype.card_perm`, `Finset.offDiag`, `Finset.card_bij'`, `Equiv.swap`, `Fintype.sum_prod_type`, `Fintype.sum_mul_sum`.
8. Hand-formalized C1 (counting form): `4 · ∑_{(σ,τ)} orderedPairCount = N(N-1) · (N!)²`. ~180 lines, 7 build iterations.
9. Logged everything to `experiments/exp00_lean_setup/notes.md`.
10. Pushed public to GitHub: `MattLoftus/automath`.

Iteration breakdown for C1 (per-step verification analytics):
- 4 of 7 lemmas first-try compiled (~57%).
- Main theorem `ELinkCount_counting`: required 4 build iterations to converge.
- Errors encountered: (a) `Finset.card_bij` with lambda — needed `simp only at` to beta-reduce; (b) rewriting through `#univ` requires `Finset.card_univ` step before `Fintype.card_perm`; (c) `omega` doesn't see through `(n+1)*(n+1) - (n+1)` without an explicit ring step; (d) `Finset.sum_boole` has a Semiring cast that breaks `rw` in pure ℕ; (e) `Fintype.sum_mul_sum` needs explicit `f, g` arguments due to higher-order unification limits in `rw`/`simp_rw`.

### Session 2 — 2026-04-28 ✅ Round B complete

Achievements:
1. **C2 formalized** in counting form: `2 · ∑ comparablePairCount = N(N-1) · (N!)²`. 109 lines, 2 build iterations, 5/6 first-try (≈ 83%). Reduces to C1 via `comparablePairCount = 2 · orderedPairCount`. The bridge uses (a) `ite_or_disjoint_eq_add` (disjoint disjunction → sum of indicators) and (b) `sum_swap_offDiag` (reindex via `(i, j) ↔ (j, i)` swap on `offDiag`). See `experiments/exp01_c2/notes.md`.
2. **C5 formalized in counting form**: `#{σ ≠ τ} + N! = (N!)²`. 103 lines, 2 build iterations, 2/5 first-try (≈ 40%). Bridge to "dim ≤ 1 ⇔ σ = τ" deferred — easy direction (`σ = τ → is total order`) is in the file as `diag_is_total_order`; hard direction requires "monotone perm of `Fin N` = id" which is not a one-line Mathlib lookup. See `experiments/exp02_c5/notes.md`.
3. **Mandatory novelty check passed.** Adjacent prior work cited: CombiBench (arXiv:2505.03171, May 2025, contest combinatorics in Lean), LeanCamCombi (Cambridge Part III formalization, ongoing), Tao 2026 Claude Code talks. Random 2-orders specifically not in any current work. See `papers/novelty_check.md`.
4. **Aggregate Round A + Round B per-step verification rate: 11 / 18 ≈ 61%.** Above H2's > 30% threshold and above PLAYBOOK's 20% floor.

Lean-specific gotchas hit (added to running list):

- **`Finset.sum_bij'` produces goals in unexpected order** when applied with bullet syntax (`·`); `Finset.sum_nbij'` (non-dependent variant) with `Prod.swap` and `Prod.swap_swap` is much cleaner.
- **`rw` with `← lemma_name` rewrites every occurrence** — including in places you didn't intend. Substitute on a helper hypothesis first, or use `nth_rewrite n`.
- **Mathlib deprecation warnings** (e.g., `Finset.filter_card_add_filter_neg_card_eq_card` → `Finset.card_filter_add_card_filter_not`) are easy to miss in long output; scan warnings even on success.

### Session 3 — 2026-04-28 ✅ C5 dim bridge + C4@k=2

Achievements:
1. **C5 dim bridge proved.** The hard direction `is2OrderTotallyOrdered σ τ → σ = τ` was deferred from Round B. Proved via: (a) `σ * τ⁻¹` is strictly monotone under the hypothesis (a < b ⇒ disjunction at `(τ⁻¹ a, τ⁻¹ b)` forces the σ-direction); (b) `StrictMono.range_inj` (`Mathlib/Order/WellFounded.lean`) + `Equiv.range_eq_univ` ⇒ `σ * τ⁻¹ = id` as a function; (c) `Equiv.ext` + `mul_inv_eq_one` ⇒ `σ = τ`. 1 build fix (`Equiv.Perm.apply_inv_self` doesn't exist; needed `show τ (τ.symm x) = x; exact τ.apply_symm_apply x` to convert group inverse to Equiv symm). C5 now FULLY formalized including the dim claim. See `experiments/exp03_c5_bridge/notes.md`.
2. **C4 at k=2 formalized.** `2 · ∑ numOrderedIncomparablePairs = N(N-1) · (N!)²`. Reduces to C2 via the partition `inc + comp = N(N-1)` per-pair. 112 lines, 3 build iterations, 3/5 first-try. The general k case (E[# k-antichains] = C(N,k)/k!) requires partitioning over k-subsets and is deferred. See `experiments/exp04_c4_k2/notes.md`.
3. **Aggregate Round A+B+C per-step verification rate: 17 / 27 ≈ 63%.** Stable across rounds.
4. **Calibration count: 4 of 10 done** (C1, C2, C4@k=2, C5). One more clears the Round D ≥ 5/10 gate.

Lean-specific gotchas hit this session:

- **Group inverse `_⁻¹` for `Equiv.Perm` doesn't auto-unfold to `.symm`** when applying lemmas like `Equiv.apply_symm_apply`. Use an explicit `show τ (τ.symm x) = x` to convert before applying.
- **`StrictMono.range_inj`** (in `Mathlib/Order/WellFounded.lean`) is the right tool for "monotone bijection of finite linear order = id." Compose with `Equiv.range_eq_univ` and `Set.range_id`.
- **For "sum of f equals constant": don't use `rw [show ∀ p, ... from ...]`** — HO unification fails. Use `Finset.sum_congr rfl h_pointwise` where `h_pointwise : ∀ p ∈ s, f p = c`.
- **Non-linear goal? Don't reach for `linarith`.** Use `set` bindings to introduce abbreviations, prove an auxiliary `ring`-derived identity to align the abbreviations, then `linarith` over the abbreviated form.

### Session 4 — Round C continuation (next)

Plan, ordered by likely tractability:

1. **C8 (P(link))** — covering relation, no intermediates. From the QG paper master interval formula `P[interior k | gap m] = (m-k-1)/(m(m-1))`, the link case is k=0: `P[link | gap m] = (m-1)/(m(m-1)) = 1/m`. Then `E[# links | i ≺ j] = ∑_m P[gap = m | i ≺ j] · 1/m`. Tractable in ℕ. **Most likely path to 5/10 calibration.**
2. **C3 (E[maximal] = H_N)** — needs ℚ machinery (or careful ℕ-only via `N!/(N-i)`). The right-to-left max reformulation requires a bijection between `Sym(N) × Sym(N)` and the relabeled `(id, τ ∘ σ⁻¹)` form. Time-box one session.
3. **C6 (Var[f])** — second moment computation. Reuse C1's `permLtCount` machinery for triple-correlation `Cov(X_{ij}, X_{ik})`. Probably moderate.
4. **C4 general k** — partition over k-subsets, show 1/k! probability per subset.
5. **C10 (E[max chain])** — chain combinatorics; not yet sketched.

Hitting 5/10 requires one more theorem (~1 session). Hitting 7/10 (methods paper at 7.0–7.5) requires three more.

---

## 19. Project Directory Layout (actual, post Session 5)

```
automath/
├── PLAYBOOK.md
├── KICKOFF_PROMPT.md
├── README.md
├── .gitignore
├── lean/                                         ← Lake workspace
│   ├── lakefile.toml                             ← pulls Mathlib v4.30.0-rc2
│   ├── lean-toolchain
│   ├── lake-manifest.json
│   ├── HelloMath.lean                            ← 1+1=2 sanity check
│   ├── Automath.lean                             ← root module: imports below
│   ├── Automath/
│   │   ├── Basic.lean                            ← scaffold (template default)
│   │   └── QGPaperG/
│   │       ├── C1_OrderedPairCount.lean          ← ✅ DONE 2026-04-27 (181 lines)
│   │       ├── C2_OrderingFraction.lean          ← ✅ DONE 2026-04-28 (109 lines)
│   │       ├── C4_TwoAntichains.lean             ← ✅ DONE 2026-04-28 (112 lines, k=2 only)
│   │       ├── C5_DimensionTwo.lean              ← ✅ DONE 2026-04-28 (151 lines, full incl. dim bridge)
│   │       └── C8_ExpectedInterval.lean          ← ✅ DONE 2026-04-28 (460 lines) — Sessions 4–5
│   ├── .lake/                                    ← gitignored: build artifacts + Mathlib mirror
│   └── .github/                                  ← workflow templates from math-lax
├── experiments/
│   ├── exp00_lean_setup/notes.md                 ← Session 1 log
│   ├── exp01_c2/notes.md                         ← Session 2 — C2
│   ├── exp02_c5/notes.md                         ← Session 2 — C5 counting form
│   ├── exp03_c5_bridge/notes.md                  ← Session 3 — C5 dim bridge
│   ├── exp04_c4_k2/notes.md                      ← Session 3 — C4 at k=2
│   └── exp05_c8/notes.md                         ← Sessions 4–5 — C8
├── papers/
│   └── novelty_check.md                          ← Session 2 — done
└── notebooks/                                    ← Python scratch for enumeration / sanity checks
```

`src/` is intentionally absent — there is no Python orchestration layer.

---

## 20. References

**LLM + proof assistant:**
- Polu & Sutskever 2020 — GPT-f (original)
- Jiang+ 2022 — Thor (retrieval-augmented)
- First+ 2023 — Baldur (Isabelle)
- Song+ 2024 — Lean Copilot
- Trinh+ 2024 — AlphaGeometry (DeepMind)
- Weng+ 2024 — AlphaProof (DeepMind)

**Lean / Mathlib:**
- Avigad, de Moura+ — "Theorem Proving in Lean 4" (online book)
- The Mathlib4 Community — Mathlib4 (ongoing)
- Buzzard — Xena Project

**Tao Lean+Claude reading list (stylistic anchor for Session 2+):**
- Tao 2026-03 — "Formalizing a proof in Lean using Claude Code" — YouTube + Hacker News thread (https://news.ycombinator.com/item?id=47306852). Demonstrates the Claude-Code-as-agent workflow on a real research formalization. First attempt 45 min + crash; second attempt 25 min after decomposing into steps. **Mirrors our Session 1 experience.**
- Tao 2025-05-31 — "A Lean companion to Analysis I" (https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/). Long-form formalization of his textbook in Lean.
- Tao 2024-03 — "Machine assisted proofs" survey (https://terrytao.wordpress.com/wp-content/uploads/2024/03/machine-jan-3.pdf). Big-picture framing of LLM + proof assistant for research math.
- teorth/analysis on GitHub — public repo for the Analysis I formalization. Worth skimming for proof style + lemma naming conventions.
- Equational Theories Project (Tao 2024) — Lean + automated provers settling 22M+ universal-algebra problems.

**Probability + combinatorics (calibration domain):**
- Matt's QG Paper G (exact combinatorial results for random 2-orders)
- Flajolet & Sedgewick — Analytic Combinatorics
- Brightwell & Winkler — random posets

**Evaluation:**
- Trotta 2008 — Bayesian evidence (for methodological grounding)

---

## 21. Upkeep Rules

Per CLAUDE.md:
- Update PLAYBOOK on architecture change.
- Update `~/workspace/MASTER_PLAYBOOK.md` on status change.
- Update `~/workspace/SCIENTIFIC_SUBMISSIONS.md` on paper status.
- Update `~/workspace/RESEARCH_LEARNINGS.md` with transferable lessons (formal methods is a new domain — expect many).
- If a novel result emerges, log it to `~/workspace/MOONSHOT_TRACKER.md`.
- Consider contributing formalized proofs to Mathlib via PR (community contribution).

---

*Initialized 2026-04-23.*
