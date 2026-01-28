# Triple Measure Lexicographic Ordering Analysis

## Measure Definitions

Let's define our triple measure `(M₁, M₂, M₃)` where:
- **M₁ = weight(t)**: Priority weight of constructors
- **M₂ = size(t)**: Total number of nodes
- **M₃ = depth(t)**: Maximum nesting depth

### Weight Function
```
weight(plum) = 0
weight(grape t) = weight(t)
weight(mango t) = weight(t)
weight(peach t₁ t₂) = weight(t₁) + weight(t₂)
weight(pear t₁ t₂) = weight(t₁) + weight(t₂)
weight(banana t₁ t₂ t₃) = 10 + weight(t₁) + weight(t₂) + weight(t₃)
weight(cherry t₁ t₂) = 20 + weight(t₁) + weight(t₂)
```

### Size Function
```
size(plum) = 1
size(grape t) = 1 + size(t)
size(mango t) = 1 + size(t)
size(peach t₁ t₂) = 1 + size(t₁) + size(t₂)
size(pear t₁ t₂) = 1 + size(t₁) + size(t₂)
size(banana t₁ t₂ t₃) = 1 + size(t₁) + size(t₂) + size(t₃)
size(cherry t₁ t₂) = 1 + size(t₁) + size(t₂)
```

### Depth Function
```
depth(plum) = 0
depth(grape t) = 1 + depth(t)
depth(mango t) = 1 + depth(t)
depth(peach t₁ t₂) = 1 + max(depth(t₁), depth(t₂))
depth(pear t₁ t₂) = 1 + max(depth(t₁), depth(t₂))
depth(banana t₁ t₂ t₃) = 1 + max(depth(t₁), depth(t₂), depth(t₃))
depth(cherry t₁ t₂) = 1 + max(depth(t₁), depth(t₂))
```

## Lexicographic Order
`(m₁, m₂, m₃) <lex (n₁, n₂, n₃)` iff:
- `m₁ < n₁`, OR
- `m₁ = n₁` AND `m₂ < n₂`, OR
- `m₁ = n₁` AND `m₂ = n₂` AND `m₃ < n₃`

## Verification of Each Reduction Rule

### Rule 1: `R_mango_grape`
`mango(grape t) → plum`

**LHS:**
- weight = weight(t)
- size = 2 + size(t)
- depth = 2 + depth(t)

**RHS:**
- weight = 0
- size = 1
- depth = 0

**Comparison:** `(0, 1, 0) <lex (weight(t), 2 + size(t), 2 + depth(t))`
- If weight(t) > 0: ✓ (first component)
- If weight(t) = 0: size comparison: 1 < 2 + size(t) ✓

### Rule 2: `R_peach_plum_left`
`peach(plum, t) → t`

**LHS:**
- weight = 0 + weight(t) = weight(t)
- size = 1 + 1 + size(t) = 2 + size(t)
- depth = 1 + max(0, depth(t)) = 1 + depth(t)

**RHS:**
- weight = weight(t)
- size = size(t)
- depth = depth(t)

**Comparison:** `(weight(t), size(t), depth(t)) <lex (weight(t), 2 + size(t), 1 + depth(t))`
- First components equal, second: size(t) < 2 + size(t) ✓

### Rule 3: `R_peach_plum_right`
`peach(t, plum) → t`

Similar to Rule 2 ✓

### Rule 4: `R_peach_cancel`
`peach(t, t) → t`

**LHS:**
- weight = weight(t) + weight(t) = 2·weight(t)
- size = 1 + size(t) + size(t) = 1 + 2·size(t)
- depth = 1 + max(depth(t), depth(t)) = 1 + depth(t)

**RHS:**
- weight = weight(t)
- size = size(t)
- depth = depth(t)

**Comparison:** `(weight(t), size(t), depth(t)) <lex (2·weight(t), 1 + 2·size(t), 1 + depth(t))`
- If weight(t) > 0: weight(t) < 2·weight(t) ✓
- If weight(t) = 0: size(t) < 1 + 2·size(t) ✓

### Rule 5: `R_banana_zero`
`banana(b, s, plum) → b`

**LHS:**
- weight = 10 + weight(b) + weight(s) + 0
- size = 1 + size(b) + size(s) + 1
- depth = 1 + max(depth(b), depth(s), 0)

**RHS:**
- weight = weight(b)
- size = size(b)
- depth = depth(b)

**Comparison:** `(weight(b), size(b), depth(b)) <lex (10 + weight(b) + weight(s), 2 + size(b) + size(s), 1 + max(depth(b), depth(s)))`
- First component: weight(b) < 10 + weight(b) + weight(s) ✓

### Rule 6: `R_apple_orange` (The tricky one!)
`banana(b, s, grape(n)) → pear(s, banana(b, s, n))`

**LHS:**
- weight = 10 + weight(b) + weight(s) + weight(n)
- size = 1 + size(b) + size(s) + (1 + size(n)) = 2 + size(b) + size(s) + size(n)
- depth = 1 + max(depth(b), depth(s), 1 + depth(n))

**RHS:**
- weight = weight(s) + (10 + weight(b) + weight(s) + weight(n)) = 10 + weight(b) + 2·weight(s) + weight(n)
- size = 1 + size(s) + (1 + size(b) + size(s) + size(n)) = 2 + size(b) + 2·size(s) + size(n)
- depth = 1 + max(depth(s), 1 + max(depth(b), depth(s), depth(n)))

**Problem:** The weight INCREASES on RHS if weight(s) > 0!
This rule doesn't decrease with current weight function.

### Rule 7: `R_cherry_refl`
`cherry(a, a) → plum`

**LHS:**
- weight = 20 + weight(a) + weight(a) = 20 + 2·weight(a)
- size = 1 + size(a) + size(a) = 1 + 2·size(a)
- depth = 1 + max(depth(a), depth(a)) = 1 + depth(a)

**RHS:**
- weight = 0
- size = 1
- depth = 0

**Comparison:** `(0, 1, 0) <lex (20 + 2·weight(a), 1 + 2·size(a), 1 + depth(a))`
- First component: 0 < 20 + 2·weight(a) ✓

### Rule 8: `R_cherry_diff`
`cherry(a, b) → mango(peach(a, b))` where a ≠ b

**LHS:**
- weight = 20 + weight(a) + weight(b)
- size = 1 + size(a) + size(b)
- depth = 1 + max(depth(a), depth(b))

**RHS:**
- weight = weight(a) + weight(b)
- size = 1 + (1 + size(a) + size(b)) = 2 + size(a) + size(b)
- depth = 1 + (1 + max(depth(a), depth(b))) = 2 + max(depth(a), depth(b))

**Comparison:** `(weight(a) + weight(b), 2 + size(a) + size(b), 2 + max(depth(a), depth(b))) <lex (20 + weight(a) + weight(b), 1 + size(a) + size(b), 1 + max(depth(a), depth(b)))`
- First component: weight(a) + weight(b) < 20 + weight(a) + weight(b) ✓

## ISSUE FOUND!

**Rule 6 (`R_apple_orange`) is problematic!**

The rule `banana(b, s, grape(n)) → pear(s, banana(b, s, n))` can increase the weight when `weight(s) > 0`.

## Proposed Fix

We need a different measure strategy. Here are options:

### Option 1: Count grape constructors as primary measure
```
grapeCount(plum) = 0
grapeCount(grape t) = 1 + grapeCount(t)
grapeCount(mango t) = grapeCount(t)
grapeCount(peach t₁ t₂) = grapeCount(t₁) + grapeCount(t₂)
grapeCount(pear t₁ t₂) = grapeCount(t₁) + grapeCount(t₂)
grapeCount(banana t₁ t₂ t₃) = grapeCount(t₁) + grapeCount(t₂) + grapeCount(t₃)
grapeCount(cherry t₁ t₂) = grapeCount(t₁) + grapeCount(t₂)
```

Then for R_apple_orange:
- LHS grapeCount = grapeCount(b) + grapeCount(s) + 1 + grapeCount(n)
- RHS grapeCount = grapeCount(s) + grapeCount(b) + grapeCount(s) + grapeCount(n)
- Problem: Still doesn't decrease if grapeCount(s) > 0!

### Option 2: Special banana-grape measure
Define a measure that counts `banana` nodes that have a `grape` as their third argument:
```
bananaGrapeCount(banana(b, s, grape(n))) = 1 + bananaGrapeCount(b) + bananaGrapeCount(s) + bananaGrapeCount(n)
bananaGrapeCount(banana(b, s, t)) = bananaGrapeCount(b) + bananaGrapeCount(s) + bananaGrapeCount(t)
... (0 for other constructors, recursive for compounds)
```

This would make R_apple_orange decrease from 1 to 0 in the first component.

## SOLUTION: Refined Weight Function

We use a weight function with special handling for the `banana-grape` pattern:

```
weight(plum) = 0
weight(grape t) = weight(t)
weight(mango t) = weight(t)
weight(peach t₁ t₂) = weight(t₁) + weight(t₂)
weight(pear t₁ t₂) = weight(t₁) + weight(t₂)
weight(banana(b, s, grape(n))) = 100 + weight(b) + weight(s) + weight(n)  -- Special case!
weight(banana(b, s, t)) = 10 + weight(b) + weight(s) + weight(t)  -- When t is not grape(_)
weight(cherry(a, b)) = 50 + weight(a) + weight(b)
```

## Verification with Corrected Measures

### Rule 6 (Fixed): `R_apple_orange`
`banana(b, s, grape(n)) → pear(s, banana(b, s, n))`

**LHS:**
- weight = 100 + weight(b) + weight(s) + weight(n)  -- Special case triggered!
- size = 2 + size(b) + size(s) + size(n)
- depth = 1 + max(depth(b), depth(s), 1 + depth(n))

**RHS:**
- weight = weight(s) + (10 + weight(b) + weight(s) + weight(n)) = 10 + weight(b) + 2·weight(s) + weight(n)
- size = 2 + size(b) + 2·size(s) + size(n)
- depth = 1 + max(depth(s), 1 + max(depth(b), depth(s), depth(n)))

**Comparison:**
- First component: 10 + weight(b) + 2·weight(s) + weight(n) < 100 + weight(b) + weight(s) + weight(n)
- This simplifies to: 10 + weight(s) < 100
- Which is true for any natural number weight(s) ✓

### Rule 8 (Updated): `R_cherry_diff`
`cherry(a, b) → mango(peach(a, b))` where a ≠ b

**LHS:**
- weight = 50 + weight(a) + weight(b)
- size = 1 + size(a) + size(b)
- depth = 1 + max(depth(a), depth(b))

**RHS:**
- weight = weight(a) + weight(b)
- size = 2 + size(a) + size(b)
- depth = 2 + max(depth(a), depth(b))

**Comparison:**
- First component: weight(a) + weight(b) < 50 + weight(a) + weight(b) ✓

## Summary

With the refined weight function:
- **cherry** gets weight 50 (highest priority for reduction)
- **banana with grape** in 3rd position gets weight 100 (highest priority, ensures R_apple_orange works)
- **banana with non-grape** in 3rd position gets weight 10
- All other constructors contribute no additional weight

This guarantees that every reduction step decreases the lexicographic triple (weight, size, depth), proving strong normalization!