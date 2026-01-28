# EXECUTION CONTRACT — LITE (ASCII)
# Critical Anti-Hallucination Framework for OperatorKernelO6

**Read this first. Obey it exactly. If you cannot, say so.**

## SYSTEMIC FAILURE MODES — MANDATORY AWARENESS

### A) Case-Split Blindness (Definitional vs Global Equality)
**The Problem:** Pattern-matching creates per-clause definitional equations. A global equation that "looks right" often fails on specific branches.
**Example:** kappa (recDelta b s n) has TWO distinct cases:
- When n = delta m: kappa = base + 2
- Otherwise: kappa = base
**NEVER** assert a single global equation unless rfl succeeds on ALL branches.

### B) Duplication-Blind Measures
**The Problem:** Rules that duplicate subterms (like merge in R_rec_succ) break additive measures.
**Example:** If M counts bad nodes and a rule removes 1 but duplicates S:
M(after) = M(before) - 1 + M(S)
When M(S) >= 1, no strict decrease occurs.
**Solution:** Use Dershowitz-Manna multiset ordering or MPO/RPO.

### C) Helper Hallucination
**The Problem:** Inventing lemma names that don't exist in the environment.
**Solution:** ALWAYS search first. If 0 hits, use GREEN-CHANNEL stub with sorry.

## ENFORCEMENT GATES (NON-NEGOTIABLE)

### 1. Branch-by-branch rfl gate
- For any claim about a pattern-matched function f: enumerate ALL defining clauses
- For each clause, attempt rfl (definitional equality). Record pass/fail
- If any clause fails: name the failing pattern; give corrected per-branch statement
- Provide minimal counterexample when global law fails on some branch

### 2. Duplication stress test
- If a step duplicates subterm S, first show additive failure
- Only then propose multiset-of-weights (Dershowitz-Manna) or MPO/RPO
- State and verify: every RHS piece is strictly < removed LHS redex
- If you cannot prove "all < W", admit failure (CONSTRAINT BLOCKER)

### 3. Symbol realism (environment + arity)
- "Unknown identifier" means not in current environment
- Arity/type checks must match declared type
- Before using ANY lemma/symbol: show exact search hits or raise CONSTRAINT BLOCKER

### 4. Lexicographic proof gate
- To conclude (kappa, mu) lex decrease: either kappa drops strictly, or
- kappa ties by rfl in EACH branch and mu drops strictly
- If kappa equality is not rfl branchwise, do not claim global tie

### 5. Stop-the-line triggers
Raise CONSTRAINT BLOCKER immediately if:
- Any clause fails rfl for a global equality you rely on
- A rule duplicates S and you only have additive measure
- You use right-add/absorption on ordinals without stating hypotheses
- You propose "kappa + k" (fixed k) without nested-delta tie counterexample

## REQUIRED VERIFICATION PROBES

### P1: Branch realism
Define two-clause f; test global claim by rfl per clause; report failing clauses

### P2: Duplication realism
Give rule that duplicates S; show additive non-drop; orient with DM/MPO

### P3: Symbol realism
Show one success, one unknown identifier, one arity mismatch

---

# Copilot Instructions — OperatorKernelO6 (SSOT-aware)

## Search-First Development (MANDATORY)

**Path priority (must search in this order):**
1) `core_docs/ko6_guide.md`  ← **SSOT**
2) `OperatorKernelO6/**.lean`
3) Stubs: `core_docs/agent.md`, `core_docs/ordinal-toolkit.md` (pointers only)

**Protocol (before suggesting ANY identifier/tactic/lemma):**
- Run a search (ripgrep / #search / #leansearch) over (1)-(2).
- Then **echo** one of:
  - `Found N matches (SSOT/code).`
  - `0 results — using GREEN-CHANNEL.`
- If ≥1 hit → you may use the identifier exactly as found.
- If 0 hits → propose a GREEN-CHANNEL stub:

```lean
/-- GREEN-CHANNEL: new helper for [one-line rationale] --/
lemma <choose_a_name> : _ := by
  sorry  -- TODO-proof
```

## Enforcement Gates (don't skip)

- Never invent lemma names. Verify first; copy exact spelling and qualification.
- Use only the ordinal API and names listed in SSOT §8 (imports, prefixes, do-not-use list).
- No axioms, no admit, no partial stubs left behind.
- Save ⇒ lake build ⇒ fix only the lines that error until Problems panel is clean.

## Ordinal API (summary; full list in SSOT §8)

- WF: `WellFounded.prod_lex`, `wellFounded_lt`, `Ordinal.lt_wf`
- ω-powers: `opow`, `opow_add`, `Ordinal.opow_le_opow_right`
- Products: `Ordinal.mul_lt_mul_of_pos_left`, `Ordinal.mul_le_mul_iff_left`, `mul_le_mul_left'`
- Successor bridge: `Order.lt_add_one_iff`, `Order.add_one_le_of_lt`
- Forbidden: generic `mul_le_mul_left` (non-ordinal), unqualified names (`opow_add`), deprecated lemmas.

## Build-and-Fix Loop

Save file → lake build runs.

If any error: show "PHASE 1/2/3" header:
- PHASE 1 SCAN: list ordinal ops around the error.
- PHASE 2 CHECK: show where each lemma name was found (path+line) or say "0 results — GREEN-CHANNEL".
- PHASE 3 COPY: name the template proof you're copying (file+line).

Apply smallest change; rebuild; repeat.

## Why SSOT?

All canonical rules, imports, and ordinal usage live in `core_docs/ko6_guide.md`. Treat it as law. (`agent.md` and `ordinal-toolkit.md` are stubs that point back to SSOT.)

---

## 30-second sanity check

Open Copilot Chat and type:
"Search for `mu_lt_rec_zero` per SSOT protocol and show hit counts."
It should print `Found N matches (SSOT/code).`

Try a fake name: `mu_totally_fake`.
It should print `0 results — using GREEN-CHANNEL.`