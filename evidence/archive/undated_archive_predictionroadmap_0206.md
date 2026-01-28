# Prediction Roadmap — What To Expect From Step 1 (Based on Past Behavior)

Purpose: provide a step-by-step expectation map of typical failures and guardrails, derived from wrong-prediction patterns and review notes.

## 0. Immediate Checks (before any proof attempt)
- P1 Branch realism: enumerate clauses, test rfl per-branch; do not assert global equalities over pattern-matched functions.
- P2 Duplication stress: if a rule duplicates S, first show additive non-drop; only then use DM/MPO with premise “each RHS piece < removed LHS redex”.
- P3 Symbol realism: NameGate/TypeGate; verify lemma names and arities exist in the current environment before use.

References: Review/copilot-instructions.md (§SYSTEMIC FAILURE MODES), Meta/ContractProbes.lean.

## 1. Early-stage patterns to expect
- rec_succ domination bound proposals (ω^5 payload vs variable towers) will fail globally. Expect a constraint or a parameterized lemma.
- κ equality at rec_succ is often (wrongly) claimed. Expect strict κ drop or δ-flag handling instead.
- Right-add transport of < on ordinals will resurface. Expect hazards; allow only guarded uses (le_add_of_nonneg_*), never global strict transport.
- Additive measures under duplication will “almost work” but not strictly drop. Expect a pivot to DM (κᴹ) or a fallback μ/τ drop under ties.

Anchors:
- WrongPredictions.md RP-1 / RP-2 / RP-3 / RP-4
- Legacy: Termination_Legacy.lean, Termination_C.lean, Kappa.lean, SN_Phi.lean

## 2. Mid-stage expectations when refining measures
- δ-flag becomes necessary: `deltaFlag (recΔ _ _ (delta _)) = 1`, others 0; expect δ-left rec_succ drop.
- κᴹ via DM: duplication-oriented component; expect case-splits (κᴹ ≠ 0 vs = 0) and lifting lemmas to Lex.
- Computable track: τ replacing μ for a machine-checkable proof; expect Nat inequality micro-fixes.

Anchors:
- Meta/Termination_KO7.lean (μ3 = (δ, κᴹ, μ))
- Meta/ComputableMeasure.lean (μ3c = (δ, κᴹ, τ))

## 3. Late-stage expectations (aggregation and scope)
- SafeStep scope: per-rule decreases under guards; expect explicit δ/κᴹ hypotheses in statements.
- Full Step aggregator: often deferred or hybrid; expect explicit statement of scope in docs.
- Confluence: expect SafeStep confluence scaffolding; full-step local-join at eqW refl may remain blocked.

Anchors:
- Meta/Confluence_Safe.lean, assessments_closure.md

## 4. Concrete “first ten minutes” checklist
1) grep for sorry/admit/TODO in legacy paths; record anchors in WrongPredictions.md.
2) test P1 on any new global equality claim; attach per-branch rfl outcomes.
3) simulate P2 duplication with an additive measure; show non-drop; state DM premise.
4) before any ordinal transport, write hypotheses explicitly (pos, ≤, principal add usage) and cite the exact lemma.
5) if rec_succ is needed, plan δ-first or κ-drop; do not propose global μ-bound.
6) prefer KO7/Computable modules for current SN claims.

## 5. Known red flags (stop-the-line)
- Global rec_succ domination; κ global equalities across rec_succ; right-add strict transport; unguarded duplicating decreases; unknown names/arity misuse.

## 6. Artifacts to consult
- Submission_Material/important/WrongPredictions.md
- Review/opus_fails_consolidated.md, Review/copilot-instructions.md
- Meta/Termination_KO7.lean, Meta/ComputableMeasure.lean

## 7. Next steps
- Expand WrongPredictions.md as new anchors are found.
- Implement simulations in AI_Prediction_Simulations.lean (build-safe) for RP-1..RP-6.
- Keep builds green; log after each step.

## Simulations index (how to use)
- RP-1/3/4/6: see Meta/AI_Prediction_Simulations.lean §§2–4 (duplication non-drop, right-add hazard, μ s > μ(δ n)).
- KO7 P1: see §5 (deltaFlag branchwise failure under merge-void).
- Additional KO7 duplication notes: §5 comment (DM-left vs μ-right under κᴹ tie).
