# Mathematical Framework for O-7 Kernel — DM Multiset Termination
*Draft created 2025-08-15 16:32 UTC*

Update 2025-08-15 18:05 UTC — Corrections
- DM order: we use `Multiset.IsDershowitzMannaLT (·<·)`, not `Multiset.R`.
- κᴹ(app a b) = κᴹ a ⊎ κᴹ b (both arguments), aligned with code.
- κᴹ ties on merge rules; we rely on μ for those branches.  κᴹ(rec_zero) is `1 :: κᴹ s` (no global strict drop claim).

---
## 1 Kernel Recap
Operators (constructors of `Trace`):
```
void        -- neutral / truth
delta t     -- dual / negation
integrate t -- cancellation probe
merge a b   -- binary combination
app s t     -- application (added in O-7)
recΔ b s n  -- primitive recursion
eqW  a b    -- propositional equality witness
```
Rewrite rules (`Step`) — eight cases (`R_*`).  See `Kernel.lean`.

---
## 2 Weight and Multiset Measure
### 2·1 Local weight `w : Trace → ℕ`
```
w(recΔ _ _ n) = w n + 1   -- increments per recursion layer
w(_)            = 0        -- all other constructors
```
### 2·2 Global multiset `κᴹ : Trace → Multiset ℕ`
```
κᴹ(void)            = ∅
κᴹ(delta t)         = κᴹ t
κᴹ(integrate t)     = κᴹ t
κᴹ(merge a b)       = κᴹ a ⊎ κᴹ b
κᴹ(app a b)         = κᴹ a ⊎ κᴹ b
κᴹ(recΔ b s n)      = (w n + 1) · κᴹ n ⊎ κᴹ s
κᴹ(eqW  a b)        = κᴹ a ⊎ κᴹ b
```
Here `·` is multiset `cons`, `⊎` multiset union.

### 2·3 Ordering
Base order: natural-number `<`.  Lift via DM-extension:
```
A <ₘ B  :=  Multiset.IsDershowitzMannaLT (<) A B
```
Well-founded because `<` on `ℕ` is.

---
## 3 Per-Rule Decrease Table (aligned with KO7 code)
| Rule | κᴹ behaviour | Proof sketch |
|------|--------------|--------------|
| int_delta          | tie          | μ strict ↓ |
| merge_void_left    | tie          | μ strict ↓ |
| merge_void_right   | tie          | μ strict ↓ |
| merge_cancel       | tie (duplicates) | μ strict ↓ |
| rec_zero           | `1 :: κᴹ s`  | use μ strict ↓ |
| rec_succ           | `{w+1}` → `{w+2}` head comparison | DM strict ↓ |
| eq_refl            | tie (κᴹ a ⊎ κᴹ a) | μ strict ↓ |
| eq_diff            | tie          | μ strict ↓ |

---
## 4 Lexicographic Combined Measure
Pair `⟨κᴹ, μ⟩` with lex order `( <ₘ , < )`.  Combined order is
well-founded ⇒ termination.

---
## 5 Implementation Checklist (updated)
1. `weight`, `κᴹ` (both args for `app`), DM order `<ₘ` — done in `Meta/Termination_KO7.lean`.
2. κᴹ lemmas: ties for int/merge/eq; value for rec_zero; strict DM drop for rec_succ — done.
3. Define δ‑flag and the triple lex `(δ, κᴹ, μ)`; implement `measure_decreases` (use μ on tie branches incl. rec_zero) and `strong_normalisation` — pending.

End of snapshot.
