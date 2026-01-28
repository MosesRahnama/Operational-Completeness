# Failure Reenactments — Step-by-Step (STRICT EXECUTION CONTRACT)

Purpose: simulate, in minimal steps, how certain proof attempts failed and how we corrected them.
Each reenactment links to WrongPredictions (RP-*) and simulations.

## RE-1: Global rec_succ domination (RP-1)
- Step 1 (naive): Propose a global bound that the recursor tail is dominated by a fixed ω^5 payload.
- Step 2 (failure): Parameter values (large μ s) defeat any fixed ω^5; global inequality not provable.
- Step 3 (fix): Use δ-flag primary (KO7) so rec_succ is handled by 1→0 drop; no global μ bound needed.
- Pointers: WrongPredictions RP-1; KO7 measure in Meta/Termination_KO7.lean; Simulations §5 (deltaFlag counterexample under merge-void shows branch-split discipline).

## RE-2: κ equality at rec_succ (RP-2)
- Step 1 (naive): Claim κ(merge s (recΔ b s n)) = κ(recΔ b s (δ n)).
- Step 2 (failure): Branch rfl check reveals rec_succ increases κ on the RHS; equality fails.
- Step 3 (fix): Either κ strictly drops (classic lex) or δ handles rec_succ (KO7).
- Pointers: WrongPredictions RP-2; SN/MuLex variants; KO7 δ-flag primary.

## RE-3: Right-add transport of < on ordinals (RP-3)
- Step 1 (naive): From a < b, conclude a + c < b + c.
- Step 2 (failure): Counterexample with c = ω: 0 < 1 but 0 + ω = 1 + ω = ω (no strictness).
- Step 3 (fix): Only use guarded lemmas (le_add_of_nonneg_*) or principal-add with exact hypotheses; avoid global strict transport.
- Pointers: WrongPredictions RP-3; Simulations §3 (right-add hazard note).

## RE-4: Duplication under additive measures (RP-4)
- Step 1 (naive): Use a node-count measure; expect strict drop on duplication (merge_cancel/eq_refl).
- Step 2 (failure): M(after) = M(before) − 1 + 2·M(S); not strictly smaller when M(S) ≥ 1.
- Step 3 (fix): Use DM (κᴹ) with premise: each RHS piece < removed LHS redex; if κᴹ = 0, fall back to μ-right.
- Pointers: WrongPredictions RP-4; KO7 proofs `drop_R_merge_cancel_zero`, `drop_R_eq_refl`; Simulations §5 (KO7 duplication mapping note).

## RE-5: μ s vs μ (δ n) global comparison (RP-6)
- Step 1 (naive): Assume μ s ≤ μ (δ n) globally.
- Step 2 (failure): Construct s = δ (δ void), n = void → μ s > μ (δ n).
- Step 3 (fix): Avoid cross-parameter global bounds; use lex components explicitly.
- Pointers: WrongPredictions RP-6; Simulations §4 (exists_mu_s_gt_mu_delta_n).

---

Use these reenactments with the Simulations index in PredictionRoadmap.md to walk the exact failure and the corrective guardrail for each class.
