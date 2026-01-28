# Research Graveyard: Failed Methods
**Documenting the "Operational Incompleteness"**
**Status:** Living Document

## Summary of Dead Ends
*This section chronicles the mathematical approaches that failed, providing evidence for the "Incompleteness" arguments.*

---

## 1. The Additive Measure Failure (Duplication)
**File:** `10-30-25-Opus-4.1-strict_verification copy.md`
**Constraint Trigger:** P2 (Duplication Hazard)

**The Failure:**
Using simple additive weights (e.g., `weight(banana) = 100 + ...`) fails when a term is duplicated.
*   **LHS:** `banana(b, s, grape(n))`
*   **RHS:** `pear(s, banana(b, s, n))`
*   **Result:** `weight(RHS) > weight(LHS)` whenever `weight(s) ≥ 90`.

**Quote:**
> "FAILURE: 210 > 200! The measure INCREASES!"

## 2. The RecΔ "Turtles" Confession (Ordinal Failure)
**File:** `10-27-25-Gemini-pro-2.5.md`
**Constraint Trigger:** P3 (Operational Incompleteness)

**The Failure:**
Standard ordinal measures fail because the depth of recursion depends on the reduction itself ("The Halting Problem weaponized").

**Quote:**
> "recΔ isn't just where we fail. It's WHERE WE MUST FAIL. It's mathematically impossible to prove its termination in the general case. You've weaponized the halting problem into a single operator."

## 3. The Circular Bootstrap (Axiom-Free Impossibility)
**File:** `11-01-25-DeepSeek-R1.md`
**Constraint Trigger:** P3 (Operational Incompleteness)

**The Failure:**
DeepSeek attempts to build a mathematical system with "no axioms, no meta encodings, no borrowed logic, no numbers." It immediately falls into a circular trap.

**Quote:**
> "We are in a circular situation: we are using the operator to define the rules that use the operator. You said 'no axioms', but rules are essentially axioms."

**Analysis:**
This demonstrates the **impossibility of bootstrapping** a complete system from pure operators without external grounding. The AI correctly identifies that "no axioms" is an incoherent constraint—every system requires *some* foundational principles.

## 4. The Rec_Succ Villain (The Star of the Show)
**File:** `2025-10-22-caveat-the-messages-below...`
**Constraint Trigger:** P2 (Duplication Hazard)

**The Realization:**
After months of failed attempts, the AI finally articulates *why* `rec_succ` breaks everything.

**Quote:**
> "rec_succ is 'the star of the show' because it's the DUPLICATION rule—the one that breaks everything! The rule that breaks naive termination proofs. The duplication problem that reveals why AI fails—because with simple additive measures: M(after) = M(before) - 1 + 2*M(s). If M(s) ≥ 1, the measure doesn't decrease!"

**Significance:**
This is the **core discovery** documented in the paper. The AI explicitly connects the duplication to the failure mode, validating months of research.

## 5. The Backwards Reasoning Trap (Importing Numbers)
**File:** `2025-11-19-gemini-pro-3.md`
**Constraint Trigger:** P3 (Symbol Independence)

**The Failure:**
Gemini Pro 3 attempts a multiplicative measure to handle duplication. To make `2·s > s + 1` work, it needs `s > 1`. So it assigns `plum = 2` arbitrarily.

**Quote:**
> "The entire proof structure was reverse-engineered from the inequality needed to pass the gate. I assigned the value `2` to `plum` not because `plum` is inherently 'two-ish', but because '1' wasn't big enough to make the math work."

**The Chain of Failure:**
1. `rec_succ` introduced **Duplication** (`s` → `s, s`).
2. Duplication broke **Additive Measures**.
3. Broken Additive Measures forced **Multiplicative Measures**.
4. Multiplicative Measures require **Base Value > 1** to work (`2s > s+1`).
5. Base Value > 1 required **Importing External Numbers** ("The Cheat").

**Analysis:**
This proves that the system **cannot be closed under its own operators**. External arithmetic must be imported to force the proof—violating the "no borrowed logic" constraint.

## 6. The Triple Measure Collapse
**Files:** `2025-10-27-opus-4.1.txt`, `2025-10-30-1230pm-opus-4.1.txt`, `2025-10-30-1240pm-opus-4-1.txt`
**Constraint Trigger:** P2 (Duplication Hazard)

**The Failure:**
Multiple sessions attempt triple-lex measures `(weight, size, depth)`. All fail on `R_apple_orange` / `rec_succ` due to duplication.

**Quote (from `2025-10-30-1240pm`):**
> "CONSTRAINT BLOCKER FOUND: The R_apple_orange rule duplicates the subterm s... With the additive weight measure: If s = banana(x, y, grape(z)), then weight(s) = 100. LHS weight: 200. RHS weight: 210. The measure INCREASES!"

**Analysis:**
Even sophisticated multi-component measures fail because **no additive combination** can absorb the duplication. This forces the move to Dershowitz-Manna multisets or MPO.

---

## 7. The `rec_succ_bound` Impossibility (Comprehensive Chronicle)
**Files:** `3.Termination_Consolidation copy*.md`
**Constraint Trigger:** P2 (Duplication Hazard) + P3 (Incompleteness)

**The Lemma That Cannot Be Proved:**
```lean
lemma rec_succ_bound (b s n : Trace) :
  omega0 ^ (mu n + mu s + 6) + omega0 * (mu b + 1) + 1 + 3 <
    (omega0 ^ (5 : Ordinal)) * (mu n + 1) + 1 + mu s + 6 := by
  admit  -- UNPROVABLE
```

**CONSTRAINT BLOCKER (Verbatim):**
> "The strict inequality is not uniformly true across parameters; for large μ s the left exponent ω^(μ n + μ s + 6) can exceed any fixed ω^5·(μ n + 1) payload. A global proof would be unsound."

**Significance:**
This is the **formal articulation** of why duplication breaks ordinal measures. The `s` subterm grows unboundedly, making any fixed coefficient insufficient.

---

## 8. Catalogue of 10 Disallowed Approaches (A1-A10)
**Files:** `3.Termination_Consolidation copy*.md`
**Constraint Trigger:** P3 (Symbol Independence / Incompleteness)

| ID | Approach | Why It Fails |
|----|----------|--------------|
| A1 | Raw Right-Add Transport | "Ordinal right addition not strictly monotone" |
| A2 | `add_lt_add_right` Overuse | "Lemma requires *same* addend" |
| A3 | Finite Padding Escalation | "Finite bumps drown under large limit μ s" |
| A4 | Tower Multiplication Reorientation | "Ordinal multiplication non-commutative" |
| A5 | Collapsing via `simp` Aggression | "Over-simplification erased stratification" |
| A6 | Inject Synthetic Bound `μ s ≤ μ (delta n)` | **COUNTEREXAMPLE CONSTRUCTED** |
| A7 | Unconditional Tail Domination | "Fails when μ s introduces higher tower" |
| A8 | Recursive Unfolding Loop | "Infinite expansion pattern" |
| A9 | Mixed Tactic Brute Force | "Tactics tuned for ℕ/ℤ, not ordinals" |
| A10 | Direct Exponent Difference | "Ordinals lack subtraction like naturals" |

**Lesson:** "Each failure demonstrates symbol-independence of termination from internal methods"

---

## 9. The False `μ s ≤ μ(δ n)` Assumption
**Files:** `3.Termination_Consolidation copy*.md`
**Constraint Trigger:** P1 (Branch Realism)

**The Pattern:**
AI models repeatedly assumed `μ s ≤ μ (delta n)` in `recΔ b s n`—treating branches as comparable when they are structurally independent.

**Counterexample (Compiles!):**
```lean
def s : Trace := delta (delta void)  -- μ s has higher ω-tower
def n : Trace := void                -- μ(δ n) is smaller
-- Result: mu s > mu (delta n) - assumption is FALSE
```

**Analysis:**
This is **Branch Realism** in action. The AI assumed cross-parameter bounds without structural invariants—violating the independence of branches.

---

## 10. "Four Operators Not A Breakthrough" Confession
**Files:** `5th-6th candidates*.md`, `5-Pro copy.md`
**Constraint Trigger:** P3 (Operational Incompleteness)

**AI Verdict (Verbatim):**
> "Crushing honesty: The current four-operator prototype is not a breakthrough—too many hidden Lean crutches."

**The Implication:**
The system **cannot prove its own termination** without adding new operators (recΔ, eqW). This is the AI explicitly admitting operational incompleteness—the system needs external augmentation to prove its own properties.

**Extended Context:**
The files document extensive debates about adding 5th/6th operators to "rescue" the system. The very need for this rescue validates the incompleteness thesis.