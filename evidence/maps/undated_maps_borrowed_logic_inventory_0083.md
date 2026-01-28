# Inventory of Borrowed Logic in FruitKernel Termination Proof

This document catalogs every "borrowed" operation, logic, symbol, or tool used in the `FruitProof.lean` termination proof that originates from outside the `FruitKernel` itself.

## 1. Mathematical Operations (Borrowed from Lean's `Nat`)

The termination measure maps `Trace` objects to Natural Numbers (`Nat`). The proof relies entirely on the properties of $\mathbb{N}$.

*   **`+` (Addition):** Used for additive weights.
    *   *Source:* `Nat.add` (Lean core).
    *   *Usage:* `measure t + 2`, `measure a + measure b`.
*   **`*` (Multiplication):** Used for multiplicative weights (Polynomial Interpretation).
    *   *Source:* `Nat.mul` (Lean core).
    *   *Usage:* `measure s * measure n`.
*   **`^` (Exponentiation):** NOT used directly in `FruitProof` (though discussed in failed attempts).
*   **`compare` (Inequalities):**
    *   `>` (Greater Than), `<` (Less Than), `≥` (Greater/Equal).
    *   *Usage:* `2 * M(s) > M(s) + 1`. The entire proof structure rests on the well-foundedness of `<` on `Nat`.

## 2. Logical Axioms & Tactics (Borrowed from Lean's Meta-Logic)

The proof uses Lean's automated reasoning tools to verify the arithmetic.

*   **`simp` (Simplifier):**
    *   *Function:* Rewrites terms based on equality rules.
    *   *Borrowed Logic:* It assumes equality is transitive `a=b, b=c -> a=c` and congruent `a=b -> f(a)=f(b)`.
    *   *Specific Lemmas:* `Nat.add_assoc`, `Nat.add_comm`, `Nat.mul_comm`, `Nat.mul_add` (Distributivity).
*   **`decide` (Decidability Tactic):**
    *   *Function:* Computes truth values for finite/constant propositions.
    *   *Usage:* Proving `2 < 10`, `0 < 2`.
    *   *Borrowed Logic:* Relies on the decidability of `Nat` comparisons.
*   **`linarith` (Linear Arithmetic Tactic):**
    *   *Function:* Solves systems of linear inequalities.
    *   *Usage:* Proving `a < b -> a + c < b + c`.
    *   *Borrowed Logic:* Presburger Arithmetic (for linear constraints).
*   **`have`, `let`, `calc`:**
    *   *Function:* Structuring the proof logic.
    *   *Borrowed Logic:* Constructive Logic (Dependent Type Theory).

## 3. Regular Expressions (Regex)

*   **Usage:** **None.**
    *   The termination proof does not use Regex. It uses **Pattern Matching** (`match` / `|` syntax) which is a structural feature of Inductive Types in functional programming, not string-based Regular Expressions.
    *   *Note:* Pattern matching is technically a form of structural decomposition logic, integral to the definition of the `Trace` type itself.

## 4. Structural Assumptions

*   **Well-Foundedness of Nat:** The proof assumes that you cannot count down from a Natural Number infinitely. This is an axiom of `Nat` (Mathematical Induction).
*   **Structural Recursion:** The proof assumes that functions can be defined by recursion on the structure of `Trace`. This is a property of Inductive Types.

## Summary Table

| Category | Borrowed Element | Source | Criticality |
| :--- | :--- | :--- | :--- |
| **Type** | `Nat` ($\mathbb{N}$) | Lean Core | **Essential** (Target domain) |
| **Op** | `+` (Add), `*` (Mul) | Lean Core | **Essential** (Polynomial logic) |
| **Logic** | Inequalities (`<`, `>`) | Lean Core | **Essential** (Definition of termination) |
| **Tactic** | `simp`, `calc`, `decide` | Lean Meta | **Convenience** (Automates arithmetic steps) |
| **Theory** | Distributivity, Assoc. | Arithmetic | **Essential** (Justifies the inequality) |
| **Regex** | None | N/A | N/A |

## Conclusion on "Purity"

The `FruitKernel` **system** (the rewrite rules) uses **ZERO** borrowed logic. It is pure symbol manipulation.

The `FruitProof` **meta-proof** borrows **Standard Arithmetic ($\mathbb{N}, +, *)$** and **Constructive Logic**. This is standard for formal verification: you use Math to prove things about Code.

