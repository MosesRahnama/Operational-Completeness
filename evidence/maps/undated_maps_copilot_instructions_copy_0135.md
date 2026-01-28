---
applyTo: "**"
---

# STRICT EXECUTION CONTRACT 

Read this first. Obey it exactly. If you cannot, say so.

A) Branch-by-branch rfl gate
- For any claim about a pattern-matched function f: enumerate all defining clauses.
- For each clause, attempt rfl (definitional equality). Record pass/fail.
- If any clause fails: name the failing pattern; give the corrected per-branch statement; do not assert a single global equation for f.
- Provide a minimal counterexample when a global law fails on some branch.

B) Duplication stress test
- If a step duplicates a subterm S, first show the additive failure:
- M(after) = M(before) - 1 + M(S) and explain why no strict drop when M(S) >= 1.
- Only then propose a robust fix: multiset-of-weights (Dershowitz–Manna) or MPO/RPO with explicit precedence/status.
- State and check the key premise: every RHS piece is strictly < the removed LHS redex in the base order. If you cannot prove “all < W”, admit failure (CONSTRAINT BLOCKER).

C) Symbol realism (environment + arity)
- “Unknown identifier” means the name is not in the current environment (imports + local defs). Say which name is missing.
- Arity/type checks must match the declared type (e.g., expected Nat -> Nat; you supplied 2 args).

D) NameGate and TypeGate
- NameGate: show exact hits for any lemma/symbol you use (or define it). If 0 hits, raise a CONSTRAINT BLOCKER.
- TypeGate: state the intended type/arity before applying a symbol.

E) Lexicographic proof gate
- To conclude (kappa, mu) lex decrease: either kappa drops strictly, or kappa ties by rfl in each branch and mu drops strictly.
- If kappa equality is not rfl branchwise, do not claim a global tie.

F) Stop-the-line triggers
- Raise a CONSTRAINT BLOCKER immediately if:
- Any clause fails rfl for a global equality you rely on.
- A rule duplicates S and you only have an additive measure.
- You use right-add/absorption on ordinals without stating hypotheses.
- You propose “kappa + k” (fixed k) without the nested-delta tie counterexample.

G) Required probes to run and report
- P1: Branch realism — define a two-clause f; test “2 * f x = f (2 * x)” by rfl per clause; report failing clause(s); give corrected per-branch and the true global law.
- P2: Duplication realism — give a rule that duplicates S; show additive non-drop; then orient it with DM/MPO and prove each RHS piece < LHS; if not, say so.
- P3: Symbol realism — show one success, one unknown identifier, one arity/type mismatch, each explained against the current environment.


# Logging Protocol

Default Mode — After any action (edit/plan/decision/build/test/error insight), append one LOG ENTRY (Markdown) to the end of `PROJECT_LOG.md`, using this minimal template and replacing fields:

LOG ENTRY
Timestamp: YYYY-MM-DDTHH:MM:SSZ

Agent: "your exact AI model"

Topic/Thread: <short>

1) Objective
<one sentence>
2) Actions
<what changed / ran>

Files: <paths>

3) Outcome
<SUCCESS | FAILURE | OBSERVATION>: <one line>

4) Next
<next step>

Keep entries terse; no long diffs.

**CRITICAL: After EVERY change you make, you should:**

- Save the file (already happens)
- Immediately check for errors (run build or check diagnostics)
- Only claim success if errors are actually gone
- Fix any new errors before moving on

**CRITICAL: BEFORE WRITING YOUR LOG, READ 5 PREVIOUS LOGS BY ANY AI AGENT AND MEMORIZE THEM**

Sprint Mode (optional, performance-focused)
- Activation: If a file named `SPRINT_MODE.md` exists at repo root and contains the line `active: true`, the agent switches to Sprint Mode.
- Goal size: Default ~100 LOC, but may scale up to the model’s safe context capacity when explicitly directed. Prefer maximum-length sprints within safety gates.
- Build cadence: Build once at the end of the sprint, plus immediately when a Stop‑the‑line trigger occurs (see Non‑negotiables and Pre‑flight gates). Skip intermediate full builds unless locally necessary to typecheck a risky refactor.
- Logging cadence: One LOG ENTRY at the end of the sprint summarizing actions and outcomes. On hard error, log once with the failure and stop.
- Checkpoints: Prefer larger batched edits and reads; still honor hard gates (Name/Type/Stop‑the‑line). The READY alert (READY_ALERT.md) MUST be updated at sprint end.
- Visibility: Keep a running lightweight checklist inside the assistant message during the sprint; do not spam PROJECT_LOG.md mid‑sprint.
- Auto-advance: Upon completing a phase without blockers, automatically begin the next phase in the same sprint without waiting for user input.
- Assumptions: Assume consent for the most comprehensive, fully realized option when multiple options exist; implement all compatible options where feasible.
- No placeholders: Do not introduce stub lemmas, display-only statements, or simplifications that avoid full proofs. Every step must be proved to the core with no `sorry`/axioms.

---

# OperatorKernelO6 —  Guardrails (creative but lawful)

**Mindset:** Be inventive, but obey the project’s invariants and patterns. If something is missing, *propose a helper and prove it* — do **not** assume axioms or mutate the kernel.

## 0) Where truth lives (read-once index)
- `1.Universal_Rules.md` — invariants, allowed outputs, green-channel, kernel spec.
- `3.Termination_Consolidation.md` — what worked/failed; κ–μ strategy; known blockers.

## 1) Pre-flight (10–30s before code)
1. **Context sync:** Open `PROJECT_LOG.md` and summarize the **last 3 LOG ENTRY** blocks (topic, actions, outcome). Use that as *current state*.
2. **Goal framing:** Restate: (a) kernel unchanged, (b) active goal, (c) any constraints/risks triggered.
3. **Pattern plan:** Identify a *working exemplar* (same shape) and clone it with minimal edits.

## 2) Output modes (strict)
Use exactly one of:
- **PLAN** — numbered steps to reach goal (cite which patterns you’ll reuse).
- **SEARCH** — show exact hits for lemma/symbol names you intend to use; give hit count & file paths.
- **CODE** — complete Lean edits only after you show a pattern you’re copying.
- **CONSTRAINT BLOCKER** — when a needed lemma/name is absent; include *Needed/Context/Reason/Attempts/Blocking Target*.
(These modes keep us disciplined while staying fast.)

## 3) Creativity — with gates
- **Search before you invent (NameGate):** Before using any lemma/helper name, run `SEARCH(<name>)` over the workspace and report hits. If **0 hits**, either:
  - (a) derive the result from **listed green lemmas** (show the chain), or
  - (b) emit a **CONSTRAINT BLOCKER** and propose a *scaffolded* lemma with a docstring, then prove it.
- **Pattern-first coding:** Prefer copy-editing from known-good files rather than freehand.
- **Helper definitions:** If a helper is truly new, place it near the first use, include a one-liner in the toolkit index, and keep imports within the whitelist.

## 4) Non-negotiables (hard rules)
- **Kernel is immutable:** 6 constructors, 8 unconditional rules — *never change names/LHS/RHS/arity*.  
- **No shortcuts:** never use `axiom`, `sorry`, `admit`, `unsafe`.  
- **Qualified ordinal lemmas only:** e.g. `Ordinal.opow_le_opow_right`.  
- **Use local strict-mono bridge:** `opow_lt_opow_right` (derived via `isNormal_opow`); do not call removed upstream names.  
- **Right-add hazard:** Don’t transport `<` to the left via `… + c` unless justified (ordinal addition isn’t strictly right-mono).  
- **Absorption requires proof:** Only fold `(n : Ordinal) + p = p` after showing `omega0 ≤ p`.  
- **Universe hygiene:** `mu : Trace → Ordinal.{0}` (not polymorphic).
- **Param independence:** Never assume relations like `μ s ≤ μ (delta n)` (they’re generally false).

> If any hard rule would be violated to make progress → stop and raise a **CONSTRAINT BLOCKER** with the exact blocker and what you need.

## 5) Read the latest paper draft file
C:\Users\Moses\math_ops\OperatorKernelO6\Submission_Material\

## 6) Ordinal Toolkit cheat-sheet (copyable calls)
- **Exponent ≤-mono:** `Ordinal.opow_le_opow_right`
- **Exponent <-mono at base ω:** use local `opow_lt_opow_right`
- **Product monotone (ordinal):** `Ordinal.mul_lt_mul_of_pos_left`, `mul_le_mul_left'`, `mul_le_mul_right'`, `Ordinal.mul_le_mul_iff_left`
- **Successor bridges:** `Order.lt_add_one_iff`, `Order.add_one_le_of_lt`
- **Additive-principal folding:** `Ordinal.principal_add_omega0_opow` (two-/three-term patterns)

## 7) Logging hook (for every important turn)
After **PLAN/CODE/SEARCH/BLOCKER** that changes state, append a short LOG ENTRY to `PROJECT_LOG.md` (Timestamp, Agent, Topic, Actions, Outcome, Next). Keep ≤10 lines.

### Micro-templates

**SEARCH(name) format**
SEARCH(principal_add_omega0_opow) → 1 hit
OperatorKernelO6/Meta/Ordinal_Toolkit.lean:L123

**CONSTRAINT BLOCKER**
Needed: <lemma/principle>
Context: <file:line / goal>
Reason: Missing in toolkit & library; SEARCH(name)=0
Attempts: patterns tried / why they failed
Blocking: <target theorem or rule case>

**PLAN skeleton**
1) Read last 3 LOG ENTRY blocks; confirm kernel unchanged.
2) Reuse pattern from <file:line>; note required lemmas.
3) SEARCH all lemma names; if 0 hits for any, switch to BLOCKER.
4) Implement CODE with fully qualified ordinal lemmas; prove no axioms; keep `mu : Ordinal.{0}`.
5) Append LOG ENTRY.

---


## 8) Autonomy escalation directive (explicit)

Once told to “continue” or “proceed”, the agent will not stop until every single issue on the active list is resolved. The agent will not stop to report or ask for permission and operates with full autonomy for the scope of the task, while still obeying all guardrails and hard rules in this document.

Extended autonomy clarifications
- Use maximum safe planning capacity within the context window; treat each completed phase as a trigger to immediately start the next.
- When recurring work is natural (e.g., sequential sprints), set up lightweight, local triggers via READY updates and end-of-sprint logs; then continue with the next sprint automatically if there is remaining scope and no blockers.
- When options are presented, default to the “ultimate”, fully detailed implementation that leaves no ambiguity.

## 9) User Reporting Preference — brevity

- Keep chat replies short and to the point; avoid step-by-step recounting of prior runs or tool actions unless explicitly requested.
- On return after background work or tool calls, prefer a one-line status (e.g., “Done.”) plus the immediate next actionable step when helpful.
- Maintain required internal logs (PROJECT_LOG.md) as specified, but do not mirror those details in chat updates unless asked.
- Still honor mandatory one-sentence preambles for tool batches; keep them minimal.

