# C) Computable Measure Roadmap (No Ordinal)

Goal: Replace Ordinal μ with a fully computable rank τ over traces, producing a computable triple-lex measure μ3c := (δ, κᴹ, τ).

## Trace-derived computable rank τ

Define τ : Trace → Nat by structural recursion; examples below are placeholders for final tuning:

- τ(void) = 0
- τ(eqW a b) = 1 + τ a + τ b
- τ(merge a b) = 1 + τ a + τ b
- τ(intΔ a n) = 1 + τ a + size(n)
- τ(recΔ b s n) = 1 + τ b + τ s + size(n)
- τ(app s t) = 1 + τ s + τ t

size(n) is a syntactic size on the delta payload (Nat), trivially computable.

Properties to target:
- τ_nonneg : ∀ t, 0 ≤ τ t
- τ_merge_dup_monotone : τ (merge t t) ≥ τ t
- τ_eq_refl_monotone   : τ (eqW a a) ≥ τ void
- τ_strict_drops per rule: Provide per-rule τ decreases or rely on κᴹ DM drop when τ ties.

## New computable measure μ3c

- δ: Nat flag, same as current deltaFlag (computable)
- κᴹ: Multiset ℕ weights (computable, already used)
- τ: as above (computable)

Orders:
- DM on κᴹ (unchanged)
- LexDM_c := Prod.Lex (DM, Nat.lt)
- Lex3c  := Prod.Lex (Nat.lt, LexDM_c)

## Replacement lemmas (full names)

- dm_to_LexDMNat_left : ∀ {X Y μ₁ μ₂}, Multiset.IsDershowitzMannaLT X Y →
  Prod.Lex (fun a b => a.IsDershowitzMannaLT b) (· < ·) (X, μ₁) (Y, μ₂)

- drop_R_eq_diff_c      : Lex3c (μ3c void) (μ3c (eq_diff a b))
- drop_R_eq_refl_c      : Lex3c (μ3c void) (μ3c (eqW a a))
- drop_R_merge_void_c   : Lex3c (μ3c t) (μ3c (merge t void))
- drop_R_merge_cancel_c : (deltaFlag t = 0) → (kappaM t = 0) → Lex3c (μ3c t) (μ3c (merge t t))
- drop_R_int_delta_c    : Lex3c (μ3c (intΔ t n)) (μ3c t)
- drop_R_rec_succ_c     : Lex3c (μ3c (app s (recΔ b s n))) (μ3c (recΔ b s (delta n)))
- drop_R_rec_zero_c     : (deltaFlag b = 0) → Lex3c (μ3c b) (μ3c (recΔ b s void))

Each follows the same schema as KO7:
- Normalize δ to α=0 when applicable.
- For κ-duplication rules, use DM-left via `dm_to_LexDMNat_left`.
- Otherwise, use τ-right strictness when available.

## Files to update (stubs first)

- OperatorKernelO6/Meta/CNFOrdinal.lean        (optional if we skip ordinals entirely for C)
- OperatorKernelO6/Meta/ComputableMeasure.lean (define τ, μ3c, LexDM_c, Lex3c, and bridges)
- OperatorKernelO6/Meta/Termination_KO7_C.lean (parallel lemmas `_c`)
- OperatorKernelO6/Meta/Ordinal_Toolkit.lean   (only if we keep A)

We’ll generate Lean skeletons with full names and `by admit`-style prose in comments (no sorry), then implement proofs iteratively.
