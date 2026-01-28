# FINAL REPORT: Termination Analysis Under Strict Contract

## Executive Summary

**CRITICAL FINDING**: The initial triple measure approach FAILS due to duplication in rule R_apple_orange. The system cannot be proven terminating with simple additive lexicographic measures.

## Required Probes Report

### P1: Branch Realism

**Test function**: `weight` with 8 branches

**Global equation tested**: `weight(banana(x, y, z)) = 10 + weight(x) + weight(y) + weight(z)`

**Results**:
- Branch 6 (`z = grape(t)`): **FAILS rfl** - Returns 100 + weight(x) + weight(y) + weight(t)
- Branch 7 (`z ≠ grape(_)`): PASSES rfl - Returns 10 + weight(x) + weight(y) + weight(z)

**Corrected per-branch law**:
```lean
weight(banana(x, y, grape(t))) = 100 + weight(x) + weight(y) + weight(t)
weight(banana(x, y, z)) = 10 + weight(x) + weight(y) + weight(z)  -- when z ≠ grape(_)
```

**True global law**: No single equation; requires pattern matching on third argument.

### P2: Duplication Realism

**Rule**: `R_apple_orange: banana(b, s, grape(n)) → pear(s, banana(b, s, n))`

**Duplication**: Subterm `s` appears once on LHS, twice on RHS.

**Additive non-drop demonstration**:
```
Let weight(s) = w
LHS weight = 100 + weight(b) + w + weight(n)
RHS weight = w + (10 + weight(b) + w + weight(n)) = 10 + weight(b) + 2w + weight(n)

For decrease: 10 + weight(b) + 2w + weight(n) < 100 + weight(b) + w + weight(n)
Requires: w < 90
```

**Counterexample**: If `s = banana(x, y, grape(z))`, then `weight(s) = 100 > 90`, causing INCREASE!

**MPO Solution**:
- Precedence: `banana >F pear`
- Orientation: `banana(b, s, grape(n)) >mpo pear(s, banana(b, s, n))`
- Proof each RHS piece < LHS:
  - `s < banana(b, s, grape(n))` ✓ (subterm property)
  - `banana(b, s, n) < banana(b, s, grape(n))` ✓ (multiset {b,s,n} << {b,s,grape(n)})

### P3: Symbol Realism

**Success case**: `Trace`, `Step`, `StepStar` - All defined in current environment ✓

**Unknown identifier**: `complexCount` in later references (after renaming to `weight`) - "Unknown identifier 'complexCount'"

**Arity mismatch**: If we tried `Step t` (1 arg) when `Step : Trace → Trace → Prop` expects 2 args - "Function expected 2 arguments, got 1"

## Constraint Blockers Identified

### BLOCKER 1: Duplication with Additive Measure
- **Rule**: R_apple_orange duplicates `s`
- **Issue**: When `weight(s) ≥ 90`, measure increases
- **Status**: Cannot use simple lexicographic ordering

### BLOCKER 2: Branch-wise rfl Failure
- **Function**: `weight` on `banana` constructor
- **Issue**: Different equations for `grape` vs non-`grape` third argument
- **Impact**: Cannot assert single global equation

## Solutions

### Solution 1: Multiset Path Ordering (MPO)
- **Status**: PROVEN TO WORK
- **Precedence**: `cherry >F banana >F pear >F peach >F mango >F grape >F plum`
- **Verification**: All rules decrease under MPO (see mpo_solution.md)

### Solution 2: Restricted System
- **Restriction**: Limit `maxBananaGrapeNesting ≤ 1`
- **Effect**: Bounds `weight(s) < 90`, making additive measure work
- **Trade-off**: Not fully general

### Solution 3: Different Measure
- **Approach**: Use interpretation into polynomials or matrices
- **Status**: Not explored

## Conclusion

The system IS terminating, but requires MPO or similar non-additive ordering. The initial triple measure approach was fundamentally flawed due to missing the duplication issue in R_apple_orange.

**Lesson**: Always check for duplication before proposing additive measures!