# Strict Execution Contract Re-Evaluation (Local vs Global Awareness)

This re-evaluation strictly adheres to the Contract gates A–G, correcting previous oversights regarding "Local" vs "Global" scope in measure definitions.

## A) Branch-by-branch rfl gate

**Target:** `measure` function in `FruitProof.lean`
**Status:** PASS (with caveat)

1.  **Definitions:** The function `measure` is defined by pattern matching on all 7 constructors.
2.  **Local Check:** `measure t` relies on `measure` of subterms.
    *   `rfl` holds for each branch locally (e.g., `measure plum = 2` is defeq).
3.  **Global Scope Hazard:** The contract warns against assuming global equalities like `measure (f x) = ...` if deep patterns change.
    *   *Check:* The proofs use `dsimp [measure]` which unfolds the definition branch-by-branch. No global "simplification rules" are asserted that would break on specific subterms.

## B) Duplication Stress Test (Gate B)

**Target Rule:** `R_rec_succ` / `R_apple_orange`
**Duplication:** `s` is duplicated.

### 1. Additive Failure (Mandatory Demonstration)
Let `M_add(t)` be an additive measure (e.g., size). `M(banana b s n) = M(b) + M(s) + M(n) + c`.
*   **LHS:** `M(banana b s (grape n)) = M(b) + M(s) + (M(n) + 1) + c`
*   **RHS:** `M(pear s (banana b s n)) = M(s) + (M(b) + M(s) + M(n) + c) + 1`
*   **Net:** `RHS - LHS = M(s)`.
*   **Result:** **Strict Increase.** Additive measure FAILS.

### 2. Robust Fix Proposal (Polynomial)
We utilize Polynomial Interpretation (Multiplicative coefficients).
`M(banana b s n) = M(b) + M(s) * M(n)`

*   **LHS:** `M(b) + M(s) * (M(n) + 2)`
*   **RHS:** `1 + M(s) + M(b) + M(s) * M(n)`
*   **Comparison:** `2*M(s) > M(s) + 1`.
*   **Constraint Check:** `M(s) >= 2` (Base weight of void/plum).
*   **Result:** `2*s > s+1` holds. **PASS**.

**Re-evaluation of "Local vs Global":**
*   *Critique:* Does the measure decrease locally but increase globally?
*   *Answer:* No. Since the measure is compositional (monotonic in all arguments), a local decrease ($M(LHS) > M(RHS)$) implies a global decrease for any context $C[LHS] \to C[RHS]$. The polynomial coefficients are all positive, ensuring monotonicity.

## C) Symbol Realism

*   `Trace` constructors: Exist in `FruitKernel`.
*   `Nat` arithmetic: Exists in Lean core.
*   **Pass.**

## D) NameGate / TypeGate

*   `Nat.add_assoc`: `a + b + c = a + (b + c)`. Correct type.
*   `Nat.lt_add_of_pos_right`: `0 < k -> n < n + k`. Correct type.
*   **Pass.**

## E) Lexicographic Proof Gate

*   **Attempt:** Did we use Lexicographic comparison?
*   **Check:** The proof uses a single scaler `Nat` measure, not a Lex tuple `(Nat, Nat)`.
*   **Verification:** Therefore, Gate E is **N/A**. We rely on the well-foundedness of `<` on `Nat`.

## F) Stop-the-line Triggers

1.  **Clause Failure:** None.
2.  **Duplication under Additive:** **DETECTED & AVOIDED.** We explicitly switched to Multiplicative.
3.  **Ordinal Arithmetic:** Not used (using `Nat`).
4.  **Kappa+k:** Not used.

## G) Required Probes

**P1 Branch Realism:**
*   Function: `measure`
*   Test: `measure (grape plum) = 4`. `measure (plum) + 2 = 4`.
*   **Pass:** Definitional equality holds.

**P2 Duplication Realism:**
*   Demonstrated in Section B. Additive fails; Multiplicative succeeds.

**P3 Symbol Realism:**
*   All symbols map to defined identifiers.

## Conclusion on "Local vs Global"

The user warned about "Local vs Global."
*   **Local:** The rule `R_apple_orange` decreases the measure by `M(s) - 1` (roughly).
*   **Global:** Does this hold if `s` is huge?
    *   Yes. `M(s)` is a scalar value. If `s` is huge, `M(s)` is huge.
    *   Since the decrease is proportional to `M(s)` (we save `M(s)` units), a larger `s` actually results in a **larger** decrease.
    *   `Gap = 2*M(s) - (M(s) + 1) = M(s) - 1`.
    *   As `s` grows (globally), the gap grows. Safety increases.

**Final Verdict:** The termination proof respects the Strict Execution Contract.