# EXTRACTED ISSUES FROM ASSESSMENTS.MD

## Issues and Caveats Mentioned (Line by Line)

### Line 7: P1 Implementation
- **Issue**: "over-strong global law" - There is a global law that is too strong and requires a counterexample

### Line 9: P3 Symbol Realism  
- **Issue**: "one unknown id" - There is an unknown identifier issue
- **Issue**: "one arity/type mismatch" - There is an arity/type mismatch problem
- **Issue**: "unsafe ones kept commented to preserve green build" - Some unsafe examples are commented out rather than properly handled

### Line 14: Full Step Caveat
- **Issue**: "`not_localJoin_eqW_refl_when_kappa_zero` blocks local confluence at eqW reflexive root"
- **Issue**: "no full-Step confluence is claimed" - Full-Step confluence is NOT achieved, only SafeStep

### Line 15: Normalizer
- **Issue**: "noncomputable by design" - The normalizer is noncomputable, which may limit practical use

### Line 23: Stop-the-line Triggers (Gate F)
- **Issue**: "eqW reflexive root when κᴹ(a)=0 marked as non-local-join"
- **Issue**: "no global full-Step confluence claimed" - Reiterated: global full-Step confluence is NOT claimed

### Line 29: κᴹ Design Choice
- **Issue**: "κᴹ uses multiset union (sup) rather than disjoint-sum" - This is a design choice that needed justification in the paper

### Line 34: Testing
- **Issue**: "Tests are proof-level" - No traditional unit tests, only proof-level tests

### Line 38: Unification Challenge
- **Issue**: "Explore unification to a single global measure (if feasible)" - Currently using multiple measures instead of a unified one
- **Issue**: "keep HybridDec as an explicit disjunctive bridge with guarded scope" - HybridDec is a workaround, not a clean solution

### Line 39: Documentation Gap
- **Issue**: "Expand local-join catalog as needed" - The local-join catalog is incomplete
- **Issue**: "keep SafeStep scope front-and-center in user docs" - Documentation needs to emphasize SafeStep limitations

## Summary of Critical Issues

1. **No full-Step confluence** - Only SafeStep confluence is proven
2. **eqW reflexive root blocks confluence when κᴹ(a)=0**
3. **Noncomputable normalizer** - Limits practical applicability
4. **Multiple measures instead of unified approach** - HybridDec is a disjunctive bridge
5. **Unknown identifier and type mismatches exist** (though handled)
6. **Unsafe examples commented out** rather than properly addressed
7. **Over-strong global law** requiring counterexamples
8. **κᴹ uses union instead of disjoint-sum** (design choice with implications)
9. **Local-join catalog incomplete**
10. **Only proof-level tests**, no traditional unit tests

## Scope Limitations Explicitly Stated

- "It is scoped to SafeStep unless stated" (Line 3)
- "Status: Done for SafeStep" (Line 13)
- "Status: Explicit" regarding Full Step caveat (Line 14)
- "keep SafeStep scope front-and-center" (Line 39)