# Multiset Path Ordering (MPO) Solution

## The Problem Recap

The rule `R_apple_orange: banana(b, s, grape(n)) → pear(s, banana(b, s, n))` duplicates the subterm `s`. With additive measures, this causes failure when `s` has high weight.

## MPO Framework

### Constructor Precedence (>F)
```
cherry >F banana >F pear >F peach >F mango >F grape >F plum
```

### Subterm Property
For MPO, we need: `t >mpo subterm(t)` for all proper subterms.

### MPO Definition
`s >mpo t` if one of:
1. `s = f(s₁,...,sₙ)` and `sᵢ ≥mpo t` for some i (subterm)
2. `s = f(s₁,...,sₙ)`, `t = g(t₁,...,tₘ)`, and either:
   - `f >F g` and `s >mpo tⱼ` for all j
   - `f = g` and `{s₁,...,sₙ} >>mul {t₁,...,tₘ}` (multiset extension)

## Verification of R_apple_orange

**LHS**: `banana(b, s, grape(n))`
**RHS**: `pear(s, banana(b, s, n))`

Need to show: `banana(b, s, grape(n)) >mpo pear(s, banana(b, s, n))`

Since `banana >F pear`, we need:
- `banana(b, s, grape(n)) >mpo s`
- `banana(b, s, grape(n)) >mpo banana(b, s, n)`

### Checking first condition: `banana(b, s, grape(n)) >mpo s`

By subterm property: `banana(b, s, grape(n)) >mpo s` ✓ (s is a direct subterm)

### Checking second condition: `banana(b, s, grape(n)) >mpo banana(b, s, n)`

Same head symbol (banana), so we need multiset comparison:
- LHS args: `{b, s, grape(n)}`
- RHS args: `{b, s, n}`

For multiset decrease, we need to show we can obtain RHS from LHS by:
- Removing some elements
- Replacing them with strictly smaller elements

Here: Remove `grape(n)`, add `n`.
Need: `grape(n) >mpo n`

By subterm property: `grape(n) >mpo n` ✓

Therefore: `{b, s, grape(n)} >>mul {b, s, n}` ✓

## Other Rules Verification

### R_mango_grape: `mango(grape(t)) → plum`
`mango >F plum` (not needed since plum has no args)
Direct by precedence ✓

### R_peach_plum_left: `peach(plum, t) → t`
Subterm property ✓

### R_peach_plum_right: `peach(t, plum) → t`
Subterm property ✓

### R_peach_cancel: `peach(t, t) → t`
Subterm property ✓

### R_banana_zero: `banana(b, s, plum) → b`
Subterm property ✓

### R_cherry_refl: `cherry(a, a) → plum`
`cherry >F plum` ✓

### R_cherry_diff: `cherry(a, b) → mango(peach(a, b))` (a ≠ b)
`cherry >F mango`, need `cherry(a, b) >mpo peach(a, b)`
Since `cherry >F peach`, need:
- `cherry(a, b) >mpo a` ✓ (subterm)
- `cherry(a, b) >mpo b` ✓ (subterm)

## Conclusion

With MPO and precedence `cherry >F banana >F pear >F peach >F mango >F grape >F plum`, all rules decrease in the ordering, proving termination!

## Key Insight

MPO handles duplication because it uses multiset comparison rather than additive weights. When `s` is duplicated in `pear(s, banana(b, s, n))`, the precedence `banana >F pear` ensures the comparison succeeds regardless of `s`'s structure.