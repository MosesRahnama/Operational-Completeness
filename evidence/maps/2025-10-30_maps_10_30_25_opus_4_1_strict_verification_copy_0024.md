# Strict Execution Contract Verification

## A) Branch-by-Branch rfl Gate for Weight Function

Testing the weight function's pattern matching branches:

```lean
def weight : Trace → Nat
  | plum => 0                                                      -- Branch 1
  | grape t => weight t                                           -- Branch 2
  | mango t => weight t                                           -- Branch 3
  | peach t₁ t₂ => weight t₁ + weight t₂                         -- Branch 4
  | pear t₁ t₂ => weight t₁ + weight t₂                          -- Branch 5
  | banana t₁ t₂ (grape t₃) => 100 + weight t₁ + weight t₂ + weight t₃  -- Branch 6 (SPECIAL)
  | banana t₁ t₂ t₃ => 10 + weight t₁ + weight t₂ + weight t₃          -- Branch 7
  | cherry t₁ t₂ => 50 + weight t₁ + weight t₂                   -- Branch 8
```

**Global equation claim**: `weight(banana(x, y, z)) = 10 + weight(x) + weight(y) + weight(z)`

- Branch 6 (when z = grape(...)): **FAILS rfl** - gives 100 + weight(x) + weight(y) + weight(z)
- Branch 7 (when z ≠ grape(...)): PASSES rfl

**Corrected per-branch statement**:
- When z matches `grape(t)`: `weight(banana(x, y, grape(t))) = 100 + weight(x) + weight(y) + weight(t)`
- Otherwise: `weight(banana(x, y, z)) = 10 + weight(x) + weight(y) + weight(z)`

## B) Duplication Stress Test for R_apple_orange

### The Critical Rule
`R_apple_orange: banana(b, s, grape(n)) → pear(s, banana(b, s, n))`

**DUPLICATION DETECTED**: Subterm `s` appears once on LHS but twice on RHS!

### Additive Failure Analysis

Using the weight measure:
- **LHS**: `banana(b, s, grape(n))`
  - weight = 100 + weight(b) + weight(s) + weight(n) [Branch 6 triggered]

- **RHS**: `pear(s, banana(b, s, n))`
  - weight = weight(s) + weight(banana(b, s, n))
  - weight = weight(s) + (10 + weight(b) + weight(s) + weight(n)) [Branch 7, since n ≠ grape(...)]
  - weight = 10 + weight(b) + 2·weight(s) + weight(n)

**Comparison**: Need 10 + weight(b) + 2·weight(s) + weight(n) < 100 + weight(b) + weight(s) + weight(n)
**Simplifies to**: weight(s) < 90

### Concrete Counterexample

Let `s = banana(a, b, grape(c))` where a, b, c are all plum:
- weight(s) = 100 + 0 + 0 + 0 = 100

Now applying R_apple_orange:
- **LHS**: `banana(b, banana(a, b, grape(c)), grape(n))`
  - weight = 100 + weight(b) + 100 + weight(n) = 200 + weight(b) + weight(n)

- **RHS**: `pear(banana(a, b, grape(c)), banana(b, banana(a, b, grape(c)), n))`
  - First part: weight(banana(a, b, grape(c))) = 100
  - Second part: weight(banana(b, banana(a, b, grape(c)), n))
    - Since n ≠ grape(...), this uses Branch 7
    - = 10 + weight(b) + 100 + weight(n) = 110 + weight(b) + weight(n)
  - Total RHS weight = 100 + 110 + weight(b) + weight(n) = 210 + weight(b) + weight(n)

**FAILURE**: 210 > 200! The measure INCREASES!

### Additive Measure Formula
```
M(after) = M(before) - removed_part + M(duplicated_s)
         = (100 + weight(b) + weight(s) + weight(n)) - 100 - weight(b) - weight(s) - weight(n)
           + 10 + weight(b) + 2·weight(s) + weight(n)
         = 10 + weight(s)
```

**No strict decrease when weight(s) ≥ 90**

## C) Symbol Realism

### Success Case
- `Trace` type: ✓ Defined in current environment
- `Step` relation: ✓ Defined with correct arity (Trace → Trace → Prop)

### Unknown Identifier Example
- Attempting to use `complexCount` in the step_decreases_measure proof would fail
- This identifier was removed and replaced with `weight`

### Arity Mismatch Example
- `weight` expects 1 argument of type Trace
- Calling `weight(t₁, t₂)` would be a type error

## D) NameGate and TypeGate

### NameGate Check
- `Prod.Lex`: ✓ Standard Lean 4 library
- `omega`: ✓ Standard tactic
- `WellFounded.apply`: ✓ Standard library function

### TypeGate Check
- `tripleMeasure`: Trace → (Nat × Nat × Nat) ✓
- `Step`: Trace → Trace → Prop ✓
- `Acc`: (α → α → Prop) → α → Prop ✓

## E) Lexicographic Proof Gate

The claimed lexicographic decrease for R_apple_orange:
- First component (weight): Should decrease from 100+w(b)+w(s)+w(n) to 10+w(b)+2w(s)+w(n)
- This requires w(s) < 90

**CONSTRAINT BLOCKER**: When w(s) ≥ 90, the first component does NOT decrease!

## F) Stop-the-Line Triggers

### CONSTRAINT BLOCKER ACTIVATED
✗ **Rule duplicates S with only additive measure**
- R_apple_orange duplicates `s`
- Additive weight measure fails when weight(s) ≥ 90
- Concrete counterexample provided above

## G) Required Probes

### P1: Branch Realism
```lean
def f : Nat → Nat
  | 0 => 0
  | n+1 => 2*n
```

Test: `2 * f x = f (2 * x)` by rfl
- Branch 1 (x = 0): 2 * 0 = f(0) → 0 = 0 ✓ rfl passes
- Branch 2 (x = n+1): 2 * (2*n) = f(2*(n+1)) → 4*n ≠ 2*(2*n+1) = 4*n+2 ✗ rfl fails

**Corrected per-branch**: No global law exists
**True law**: f(0) = 0 and f(n+1) = 2*n

### P2: Duplication Realism
Rule: `banana(b, s, grape(n)) → pear(s, banana(b, s, n))`
- Duplicates: s
- Additive non-drop shown above: M increases when weight(s) ≥ 90

**MPO Orientation Attempt**:
- Need: Each RHS piece < LHS in base order
- RHS pieces: `s` and `banana(b, s, n)`
- Must prove: `s < banana(b, s, grape(n))` and `banana(b, s, n) < banana(b, s, grape(n))`
- First: ✓ (subterm property)
- Second: ✓ (multiset {b,s,grape(n)} >> {b,s,n} since grape(n) > n)

### P3: Symbol Realism
- **Success**: `size : Trace → Nat` compiles correctly
- **Unknown identifier**: Using `complexCount` would fail (removed from code)
- **Arity mismatch**: `size(t₁, t₂)` would fail - size expects 1 arg, got 2

## FINAL VERDICT

**The additive triple measure approach is INCORRECT** due to duplication in R_apple_orange.

The MPO solution is the correct approach because:
1. It handles duplication via multiset comparison
2. All RHS subterms are provably smaller than LHS
3. The precedence `banana >F pear` ensures termination

**The proof in Kernel.lean contains a FATAL FLAW** - the step_decreases_measure theorem is false for certain inputs!