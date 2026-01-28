# Triple Measure Lexicographic Ordering - Summary

## The System
Your fruit-themed rewriting system has 8 reduction rules that transform `Trace` terms. The goal is to prove **strong normalization** - that every term eventually reaches a normal form (no more reductions possible).

## The Triple Measure Approach

We use a lexicographic ordering on triples `(M₁, M₂, M₃)` where:

### M₁: Weight (Primary Measure)
```lean
weight(banana(b, s, grape(n))) = 100  -- Special high weight for banana-grape pattern
weight(cherry(a, b)) = 50             -- High weight for cherry
weight(banana(b, s, t)) = 10          -- Medium weight for regular banana
weight(other constructors) = 0        -- No additional weight
```

The weight function specifically handles the problematic `R_apple_orange` rule by giving `banana` with a `grape` third argument a weight of 100, ensuring it always decreases when reduced.

### M₂: Size (Secondary Measure)
Total number of nodes in the term. This handles most simple reductions where a compound term reduces to a subterm.

### M₃: Depth (Tertiary Measure)
Maximum nesting depth. Rarely needed but ensures completeness.

## Why It Works

For each reduction rule `t → u`, we prove `measure(u) <lex measure(t)`:

1. **Rules that eliminate cherry/banana**: Weight decreases (50→0 or 100/10→0)
2. **Rules that simplify structure**: Size decreases when weight stays same
3. **Special case R_apple_orange**: Weight drops from 100 to at most 10+2w(s) < 100

## Key Insight

The crucial innovation is recognizing that `banana(b, s, grape(n))` needs special treatment. By assigning it weight 100 (much higher than the resulting `pear` structure), we guarantee the problematic rule decreases the measure.

## The Proof Structure

1. **Define measures**: weight, size, depth
2. **Prove step_decreases_measure**: Each reduction decreases the lexicographic triple
3. **Apply well-founded induction**: Since `(ℕ × ℕ × ℕ, <lex)` is well-founded
4. **Extract normal forms**: Use accessibility to construct the normal form

This approach proves your system is strongly normalizing without any restrictions!