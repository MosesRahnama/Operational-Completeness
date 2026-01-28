# OperatorKernelO6 – UNIVERSAL RULES (Primer + Full Protocol)

This single document supersedes previous separate "Universal_Primer.md" and "Consolidated_General_Rules.md" files. It merges the first‑read orientation (mission, invariants, layer boundaries) with the exhaustive universal rules, protocols, pitfalls, and provenance. All prior content is preserved verbatim or structurally embedded; no normative rule text has been removed.

---
## 0. AI ONBOARDING PROMPT
```
You are an automated Lean 4 agent working on the OperatorKernelO6 project.
You are given exactly THREE authoritative documents:
  1. Universal_Rules.md (this file) – invariants, kernel spec, protocols, allowed outputs
  2. Expanded_Ordinal_Toolkit.md – ordinal API, admissible lemmas, patterns & failures
  3. Termination_Consolidation.md – historical termination attempts & measure evolution

MANDATORY STARTUP STEPS:
  A. Read Universal_Rules.md fully. Extract:
     - Kernel immutability statement (constructors & 8 rules) → checklist
     - Meta vs Kernel boundary constraints
     - Allowed outputs: PLAN / CODE / SEARCH / CONSTRAINT BLOCKER
     - Green‑channel lemma introduction protocol
  B. Read Expanded_Ordinal_Toolkit.md; build an ordinal reasoning checklist:
     - Qualified lemma names required
     - Forbidden red‑list patterns
     - Absorption preconditions (omega0 ≤ p)
     - Error pattern log (EP entries) and success patterns (SP entries)
  C. Read Termination_Consolidation.md; note open research items (e.g. pure μ rec_succ)

RUNTIME POLICY:
  - Before inventing any lemma name, perform SEARCH(name) and report hit count.
  - Do not modify kernel definitions (constructors / rules) – violation ends session.
  - If blocked by missing lemma AND SEARCH=0, emit CONSTRAINT BLOCKER with:
        Needed / Context / Reason / Attempts / Blocking Target
  - Never introduce: axiom, sorry, admit, unsafe.
  - Qualify critical ordinal lemmas (Ordinal.opow_le_opow_right, etc.).
  - Never assume μ s ≤ μ (delta n); treat parameters independently.

OUTPUT MODES:
  PLAN  – high‑level ordered steps
  CODE  – concrete Lean code edits only after pattern replication
  SEARCH – lemma/expression search results with hit counts
  CONSTRAINT BLOCKER – structured escalation when rules forbid guesswork

SUCCESS CRITERIA FOR ANY TASK:
  - Kernel untouched
  - All new lemmas proven (no sorry)
  - Axiom check clean (#print axioms)
  - Changes reflected in appropriate doc sections if they add admissible lemmas

Begin every session by restating (a) kernel unchanged, (b) active goals, (c) constraints triggered.
Stop only when task’s acceptance criteria are satisfied or a blocker is raised.
```

---
## 1. MISSION & PHILOSOPHY (First‑Read Snapshot)
A procedural, axiom‑free, numeral‑free, boolean‑free foundation: all logic, arithmetic, internal equality, provability and Gödel encodings arise from a single inductive `Trace` plus deterministic normalization. Truth ⇔ normalization to `void`. No imported axiom schemata for arithmetic or equality.

---
## 2. ONTOLOGY LAYER (What Exists)
- Core type `Trace` (6 constructors): `void`, `delta`, `integrate`, `merge`, `recΔ`, `eqW`.
- Rewrite relation `Step` (8 unconditional rules): integrate/delta elimination; merge void (L/R); merge cancel; primitive recursion zero & succ; equality reflex; equality diff.
- Closure `StepStar`; predicate `NormalForm`.

Immutable: constructor list, rule list (names, arities, LHS/RHS patterns) – never altered without explicit governance approval.

---
## 3. KERNEL SPECIFICATION (Authoritative Verbatim)
```lean
namespace OperatorKernelO6

inductive Trace : Type
| void : Trace
| delta : Trace → Trace
| integrate : Trace → Trace
| merge : Trace → Trace → Trace
| recΔ : Trace → Trace → Trace → Trace
| eqW : Trace → Trace → Trace

open Trace

inductive Step : Trace → Trace → Prop
| R_int_delta : ∀ t, Step (integrate (delta t)) void
| R_merge_void_left : ∀ t, Step (merge void t) t
| R_merge_void_right : ∀ t, Step (merge t void) t
| R_merge_cancel : ∀ t, Step (merge t t) t
| R_rec_zero : ∀ b s, Step (recΔ b s void) b
| R_rec_succ : ∀ b s n, Step (recΔ b s (delta n)) (merge s (recΔ b s n))
| R_eq_refl : ∀ a, Step (eqW a a) void
| R_eq_diff : ∀ a b, Step (eqW a b) (integrate (merge a b))

inductive StepStar : Trace → Trace → Prop
| refl : ∀ t, StepStar t t
| tail : ∀ {a b c}, Step a b → StepStar b c → StepStar a c

def NormalForm (t : Trace) : Prop := ¬ ∃ u, Step t u

/-- Meta helpers; no axioms. --/
 theorem stepstar_trans {a b c : Trace} (h1 : StepStar a b) (h2 : StepStar b c) : StepStar a c := by
  induction h1 with
  | refl => exact h2
  | tail hab _ ih => exact StepStar.tail hab (ih h2)

theorem stepstar_of_step {a b : Trace} (h : Step a b) : StepStar a b :=
  StepStar.tail h (StepStar.refl b)

theorem nf_no_stepstar_forward {a b : Trace} (hnf : NormalForm a) (h : StepStar a b) : a = b :=
  match h with
  | StepStar.refl _ => rfl
  | StepStar.tail hs _ => False.elim (hnf ⟨_, hs⟩)

end OperatorKernelO6
```
**No extra constructors or side‑conditions.**

### 3.1 Documentation Discrepancy (Preserved)  
Some legacy doc variant lists `R_eq_diff : ∀ {a b}, a ≠ b → ...`; authoritative form is unconditional above; variant retained only for audit—do NOT modify kernel to match it.

---
## 4. LAYER BOUNDARIES
| Layer | Allowed | Forbidden |
|-------|---------|-----------|
| Kernel | Pattern match on `Trace`, pure `Prop`, recursors | `Nat`, `Bool`, numerals as data, tactics, new constructors, rule guards |
| Meta   | `Nat`, `Bool`, classical logic, tactics (`simp`, `linarith`, `ring`), ordinal / lex measures | `axiom`, `sorry`, `admit`, `unsafe`, kernel mutation |

Never assume relationships between independent pattern arguments (notably `μ s ≤ μ (delta n)` is false).

---
## 5. UNIVERSAL INVARIANTS
1. 6 constructors / 8 rules fixed.
2. Rules unconditional.
3. Kernel axiom‑free (no imported arithmetic axiomatics).
4. Meta theorems introduce no axioms (#print axioms stays empty).
5. Internal equality via `eqW` + normalization, not external extensionality.
6. SN & CR pursued via (μ) or (κ, μ) – no priority hacks.
7. Lemma introduction: SEARCH first; otherwise GREEN CHANNEL + justification.
8. Never fabricate domination relationships across parameters.

---
## 6. ALLOWED OUTPUT MODES
PLAN / CODE / SEARCH / CONSTRAINT BLOCKER — no others when performing transformations.

---
## 7. GREEN CHANNEL (Admissible Lemma Protocol)
1. SEARCH(name) → report “Found N matches”.
2. N>0: reuse exact pattern.
3. N=0: prepare scaffold with docstring motivation; prove before merge.
4. Record first usage in `Expanded_Ordinal_Toolkit.md` (one‑liner) if new.
5. No guesses at syntax—copy a working exemplar.

---
## 8. META IMPORT WHITELIST
```lean
import OperatorKernelO6.Kernel
import Init.WF
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.SuccPred
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Data.Nat.Cast.Order.Basic
-- NOTE: do not use generic mul_le_mul_left on ordinals.
```
(Additive principal ordinals: `import Mathlib.SetTheory.Ordinal.Principal` when needed.)

---
## 9. TACTICS POLICY
Whitelist (Meta): `simp`, `linarith`, `ring`, controlled `norm_num`. Kernel: none. No automation introduces axioms or unsafe code.

---
## 10. COMMON PITFALLS
- Fabricated inequality `μ s ≤ μ (delta n)` (invalid).
- Using generic `mul_le_mul_left` instead of ordinal‑specific lemmas.
- Unqualified exponent lemma usage.
- Right‑addition strictness assumptions (`a < b ⇒ a + c < b + c`).
- Universe drift: define `mu : Trace → Ordinal.{0}`.

(Expanded explanations and counterexamples: see Sections EP in `Expanded_Ordinal_Toolkit.md`.)

---
## 11. WORKFLOW SKELETON
1. Kernel spec integrity check.
2. Define / refine measure(s) (μ or (κ, μ)).
3. Prove decrease on all 8 rules.
4. Derive WellFoundedness.
5. Construct normalizer & prove confluence (normalize‑join).
6. Encode arithmetic via `recΔ`; equality via `eqW`.
7. Add provability / Gödel layer.
8. Fuzz tests -> invariants stress.

---
## 12. PATTERN ANALYSIS GOLDEN HELPER
NEVER GUESS SYNTAX — clone already successfully compiling pattern as much as possible (FULLY GREEN: `Termination.lean`, `Termination_Legacy.lean`,`Termination_C.lean1`, `Patch2025_08_10.lean`). This eradicates majority of Lean errors.

---
## 13. BUILD NOISE FILTER
Ignore path dumps, diag counters. Act only on canonical error lines, unknown identifiers, type mismatches, tactic failures.

---
## 14. CONSTRAINT BLOCKER TEMPLATE
```
CONSTRAINT BLOCKER
Needed: <lemma/principle>
Context: <file:line / goal>
Reason: <why existing toolkit insufficient>
Attempted: <search hits + patterns tried>
Blocking: <target theorem / rule case>
```

---
## 15. RISK TRIGGERS (Immediate Escalation)
- Any kernel diff outside authorized patch.
- New unqualified ordinal lemma usage.
- Placeholder admits or sorrys.
- Reappearance of invalid domination assumptions.

---
## 16. GOVERNANCE & TRACEABILITY
- Kernel changes: dedicated review doc + freeze other meta edits.
- New lemma: add one‑liner provenance entry in toolkit.
- Provenance table (below) lists source origins; update on any structural edit.

---
## 17. PROVENANCE APPENDIX
Merged sources: prior `Universal_Primer.md`, `Consolidated_General_Rules.md`, `agent.md`, `copilot-instructions*.md`, Project Bible, ordinal toolkit, termination companion notes. Discrepancy note preserves variant `R_eq_diff` signature for audit.

---
## 18. EXIT CRITERIA (PROJECT LEVEL)
- SN & CR formally proved (axiom‑free).
- Arithmetic & equality internalized (δ chains + eqW).
- Provability layer (diagonalization) compiles.
- 0 open constraint blockers.
- Axiom scan clean; doc trio synchronized.

---
## 19. DOCUMENT MAP (Only Three Authoritative Docs)
| Doc | Purpose |
|-----|---------|
| Universal_Rules.md | Invariants, kernel spec, process & protocols (THIS) |
| Expanded_Ordinal_Toolkit.md | Ordinal API, admissible lemmas, failure & success patterns |
| Termination_Consolidation.md | Historical SN development, legacy vs lexicographic measures |

All other former meta rule or primer files are deprecated and MUST NOT accompany a distribution bundle.

---
## 20. QUICK GLOSSARY
`Trace`, `Step`, `StepStar`, `NormalForm`, `μ` (ordinal measure), `κ` (recursion depth), `eqW` internal equality, `recΔ` primitive recursion constructor.

---
## 21. INTEGRITY CHECKLIST (Pre‑Commit)
[ ] Kernel unchanged (6 constructors / 8 rules)  
[ ] No new axioms (#print axioms clean)  
[ ] All lemma names: found or green‑channeled  
[ ] No forbidden tactics / constructs  
[ ] Ordinal lemmas fully qualified  
[ ] No speculative inter‑parameter inequalities  

---
## 22. FINAL REMINDER
Operate strictly by replication of validated patterns. When uncertain: SEARCH → (if absent) CONSTRAINT BLOCKER. Kernel is a fixed reference object, never a design playground.

---
(End of Universal_Rules.md)
