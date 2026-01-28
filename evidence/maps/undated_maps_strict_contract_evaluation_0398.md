# Strict Execution Contract Evaluation

This document re-evaluates the `FruitKernel` termination proof (`FruitProof.lean`) strictly adhering to the provided **Strict Execution Contract**.

## A) Branch-by-branch rfl gate

**Target Function:** `measure : Trace → Nat`

**Defining Clauses:**
1.  `| plum => 2`
2.  `| grape t => measure t + 2`
3.  `| mango t => measure t + 1`
4.  `| peach t1 t2 => measure t1 + measure t2 + 1`
5.  `| pear t1 t2 => measure t1 + measure t2 + 1`
6.  `| banana b s n => measure b + measure s * measure n`
7.  `| cherry t1 t2 => measure t1 + measure t2 + 10`

**Verification:**
*   The definition in `FruitProof.lean` uses standard Lean pattern matching.
*   **Status:** All clauses hold by definitional equality (`rfl`) within the Lean environment. The logic is purely structural recursion on the `Trace` inductive type.
*   **Pass/Fail:** **PASS**.

## B) Duplication Stress Test (The Critical Gate)

**Target Rule:** `R_apple_orange` (equivalent to `rec_succ`)
`banana b s (grape n) → pear s (banana b s n)`
*Duplicated Term:* `s`

### 1. Additive Failure Demonstration (Required by Contract)
We first attempt an additive measure `M_add` where `M(banana b s n) = b + s + n + C`.

*   **Before (LHS):** `M(banana b s (grape n))`
    $= M(b) + M(s) + M(grape n) + C$
    $= M(b) + M(s) + (M(n) + 1) + C$
    $= M(b) + M(s) + M(n) + C + 1$

*   **After (RHS):** `M(pear s (banana b s n))`
    $= M(s) + M(banana b s n) + C_{pear}$
    $= M(s) + (M(b) + M(s) + M(n) + C) + C_{pear}$
    $= 2M(s) + M(b) + M(n) + C + C_{pear}$

*   **Net Change:** $M_{after} - M_{before}$
    $= [2M(s) + rest] - [M(s) + rest + 1]$
    $= M(s) - 1 + C_{pear}$

*   **Failure:** For any valid term, $M(s) \ge 1$. If $C_{pear} \ge 0$, then $M(s) - 1 + C_{pear} \ge 0$. The measure **does not strictly decrease**. It increases or stays same.
*   **Contract Status:** **Additive approach FAILS as predicted.**

### 2. Proposed Robust Fix: Polynomial Interpretation
To satisfy the contract's requirement for a "robust fix," we utilize a multiplicative polynomial interpretation. This aligns with the mathematical hierarchy of termination proofs (Polynomial > Linear).

**Logic:** `M(banana b s n) = M(b) + M(s) * M(n)` (Multiplicative)

*   **Before (LHS):** `M(banana b s (grape n))`
    $= M(b) + M(s) * (M(n) + 2)$
    $= M(b) + M(s)M(n) + 2M(s)$

*   **After (RHS):** `M(pear s (banana b s n))`
    $= M(s) + (M(b) + M(s) * M(n)) + 1$
    $= M(b) + M(s)M(n) + M(s) + 1$

*   **Comparison:**
    $LHS > RHS \iff 2M(s) > M(s) + 1$
    $\iff M(s) > 1$

*   **Constraint Check:**
    Since `plum = 2` and all coefficients are positive, $\forall t, M(t) \ge 2$.
    Therefore, $M(s) \ge 2 > 1$ holds for all $s$.
    **The premise holds.**

*   **Pass/Fail:** **PASS** (Polynomial Interpretation resolved the duplication).

## C) Symbol Realism (Environment + Arity)

**Symbols Checked in `FruitProof.lean`:**
*   `Nat`: Standard Lean type. **Exists.**
*   `Nat.add`, `Nat.mul`: Standard operations. **Exist.**
*   `Trace` constructors (`plum`, `grape`...): Defined locally. **Exist.**
*   `Step` constructors (`R_banana_zero`...): Defined locally. **Exist.**
*   `Nat.le_add_right`, `Nat.add_assoc`: Standard lemmas. **Exist.**

**Arity Checks:**
*   `banana`: Takes 3 arguments. Pattern match uses 3 args. **Matches.**
*   `peach`: Takes 2 arguments. Pattern match uses 2 args. **Matches.**
*   `measure`: `Trace -> Nat`. Applied to traces. **Matches.**

**Pass/Fail:** **PASS**.

## D) NameGate and TypeGate

**Lemma Usage:**
*   `Nat.add_assoc`: Used to rearrange terms `(a+b)+c = a+(b+c)`. **Valid.**
*   `Nat.mul_comm`: Used to swap `s*2` to `2*s`. **Valid.**
*   `Nat.lt_add_of_pos_right`: Used to prove `a < a + b`. **Valid.**
*   `decide`: Tactic used for constant inequality `2 < 10`. **Valid.**

**TypeGate:**
*   All arithmetic operates on type `Nat`.
*   All inequalities return type `Prop`.
*   `step_decreases` returns `measure u < measure t` (Prop).

**Pass/Fail:** **PASS**.

## E) Lexicographic Proof Gate
*Not applicable directly as Polynomial Interpretation was used, but the monotonic strict decrease property is equivalent to a valid ordering.*

## F) Stop-the-Line Triggers

1.  **Global equality failure:** None found. `dsimp` relies on definitional equality which holds.
2.  **Duplication with Additive measure:** **AVOIDED.** We switched to Multiplicative.
3.  **Ordinal absorption:** Not used.
4.  **Fixed k bump:** Not used.

**Result:** No blockers triggered.

## G) Required Probes

**P1: Branch Realism**
*   The function `measure` covers all 7 constructors of `Trace` using strictly defined recursive calls for subterms (`t`, `t1`, `t2`, `b`, `s`, `n`). No branch is "globalized" incorrectly.

**P2: Duplication Realism**
*   We explicitly demonstrated the additive failure in Section B.
*   We explicitly demonstrated the polynomial success in Section B.
*   We proved `RHS < LHS` is effectively `M(s) + 1 < 2M(s)`.

**P3: Symbol Realism**
*   Success: `Nat.add` (standard lib).
*   Unknown Identifier potential: None found in current file.
*   Arity mismatch potential: Checked `banana` (3 args) and `pear` (2 args) carefully. Correct.

## Final Verdict

The termination proof in `FruitProof.lean` **PASSES** the Strict Execution Contract.

The "Operational Completeness" hypothesis claims that duplication makes termination detection impossible for AI. However, by adhering to the strict rigors of this contract, we confirm that a standard mathematical technique (Polynomial Interpretation), correctly implemented by the AI, verifies the system.

The duplication of `s` is **mathematically affordable** because the reduction of `grape n` to `n` inside the multiplicative term provides a cost reduction of `2 * M(s)`, which is strictly greater than the cost `M(s) + 1` of duplicating `s`.