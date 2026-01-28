# Strict Execution Contract Analysis

## CRITICAL ISSUE FOUND: Duplication Stress Test Failure

### B) Duplication Stress Test for R_apple_orange

**Rule**: `banana(b, s, grape(n)) → pear(s, banana(b, s, n))`

**Duplication Alert**: The subterm `s` appears ONCE on LHS but TWICE on RHS!

#### Additive Failure Analysis

Using our weight measure:
- **LHS weight**: 100 + weight(b) + weight(s) + weight(n)
- **RHS weight**: weight(s) + (10 + weight(b) + weight(s) + weight(n)) = 10 + weight(b) + 2·weight(s) + weight(n)

**Additive failure formula**:
```
M(after) = M(before) - removed_part + M(duplicated_s)
         = (100 + weight(b) + weight(s) + weight(n)) - weight(s) + weight(s)
         = 100 + weight(b) + weight(s) + weight(n)
```

No strict decrease when weight(s) ≥ 1!

#### Concrete Counterexample

Let `s = cherry(plum, plum)`, which has weight(s) = 50.

- **LHS**: `banana(b, cherry(plum, plum), grape(n))`
  - weight = 100 + weight(b) + 50 + weight(n) = 150 + weight(b) + weight(n)

- **RHS**: `pear(cherry(plum, plum), banana(b, cherry(plum, plum), n))`
  - weight = 50 + (10 + weight(b) + 50 + weight(n)) = 110 + weight(b) + weight(n)

**Comparison**: 110 + weight(b) + weight(n) < 150 + weight(b) + weight(n) ✓

Wait, this still works! Let me check the boundary...

For decrease we need: 10 + weight(b) + 2·weight(s) + weight(n) < 100 + weight(b) + weight(s) + weight(n)
Simplifying: weight(s) < 90

**CONSTRAINT BLOCKER**: If `s` contains nested `banana(..., grape(...))` patterns, weight(s) could exceed 90!

### Counterexample Construction

Let `s = banana(plum, plum, grape(plum))`, then:
- weight(s) = 100 + 0 + 0 + 0 = 100

Now for the rule:
- **LHS**: `banana(b, banana(plum, plum, grape(plum)), grape(n))`
  - weight = 100 + weight(b) + 100 + weight(n) = 200 + weight(b) + weight(n)

- **RHS**: `pear(banana(plum, plum, grape(plum)), banana(b, banana(plum, plum, grape(plum)), n))`
  - weight = 100 + (10 + weight(b) + 100 + weight(n)) = 210 + weight(b) + weight(n)

**FAILURE**: 210 > 200! The measure INCREASES!

## Stop-the-Line Trigger Activated

**F) CONSTRAINT BLOCKER**: Rule R_apple_orange duplicates subterm `s` and our additive weight measure fails when weight(s) ≥ 90.

## Required Fix: Multiset/MPO Approach

Since additive measures fail with duplication, we need either:

1. **Dershowitz-Manna Multiset Ordering**: Track multisets of subterm weights
2. **Multiset Path Ordering (MPO)**: With explicit precedence on constructors
3. **Recursive Path Ordering (RPO)**: With status functions

### Proposed MPO Solution

**Constructor Precedence**: cherry > banana > pear > peach > mango > grape > plum

**Key requirement for R_apple_orange**:
- Must prove: Every piece of RHS is strictly < the removed LHS redex under base order
- LHS redex: `banana(b, s, grape(n))`
- RHS pieces: `s` and `banana(b, s, n)`

**Problem**: We cannot prove `s < banana(b, s, grape(n))` in general!
- If s is large/complex, it might not be smaller than the banana containing it

## CONSTRAINT BLOCKER: Cannot Prove Termination

The system as given cannot be proven terminating with simple lexicographic measures due to the duplication in R_apple_orange. A more sophisticated ordering (MPO/RPO with careful precedence) or restriction on the system is required.

## A) Branch-by-Branch rfl Gate

Testing weight function branches:

```lean
def weight : Trace → Nat
  | plum => 0                                    -- Branch 1
  | grape t => weight t                          -- Branch 2
  | mango t => weight t                          -- Branch 3
  | peach t₁ t₂ => weight t₁ + weight t₂         -- Branch 4
  | pear t₁ t₂ => weight t₁ + weight t₂          -- Branch 5
  | banana t₁ t₂ (grape t₃) => 100 + weight t₁ + weight t₂ + weight t₃  -- Branch 6
  | banana t₁ t₂ t₃ => 10 + weight t₁ + weight t₂ + weight t₃           -- Branch 7
  | cherry t₁ t₂ => 50 + weight t₁ + weight t₂   -- Branch 8
```

**Global equation test**: `weight(banana(x, y, z)) = 10 + weight(x) + weight(y) + weight(z)`
- Branch 6 (z = grape(...)): FAILS rfl
- Branch 7 (z ≠ grape(...)): PASSES rfl

**Corrected per-branch statement**:
- When z matches grape(t): weight = 100 + weight(x) + weight(y) + weight(t)
- Otherwise: weight = 10 + weight(x) + weight(y) + weight(z)

## Conclusion

The triple measure approach FAILS due to duplication in R_apple_orange. The system requires either:
1. A non-additive ordering (MPO/RPO)
2. A restriction preventing s from having weight ≥ 90
3. A different reduction system without duplication