# Assessments Closure Notes

This note addresses and closes the concrete gaps identified in `assessments.md` from the perspective of the KO7 SafeStep results.

1) Single-measure scope (SafeStep)
- All termination decreases in `OperatorKernelO6/Meta/Termination_KO7.lean` use one measure: μ3 := (δ-flag, κᴹ, μ) under Lex3.
- We explicitly scope strong-normalization to SafeStep. We do not claim SN for full Step in this module.
- Where the larger project discusses a “hybrid” measure, it is not used by the SafeStep SN results. This avoids the disjunction issue for this scope.

2) Confluence scope
- `Confluence_Safe.lean` proves local confluence and Newman for SafeStep only.
- `not_localJoin_eqW_refl_when_kappa_zero` documents the full Step failure. The paper/code will state this limitation prominently.

3) κᴹ union design rationale
- κᴹ uses multiset union (∪) at app/merge/eqW to capture duplication without inflating counts beyond necessary witnesses.
- The DM orientation lemmas in `Termination_KO7.lean` are checked per-rule against this definition. This is a deliberate deviation from sum-based variants and is compatible with our proofs.

4) Normalizer status
- The SafeStep normalizer is provided via well-founded recursion and is noncomputable. It is a proof-producing extractor, not an executable algorithm.

5) Required probes (A–G) pointers
- A) Branch-by-branch rfl: κᴹ simp lemmas show the per-constructor equalities; duplicating cases avoid asserting global ties.
- B) Duplication stress: handled via DM orientation and explicit witnesses (see dm_lt_add_of_ne_zero' and κᴹ duplicate lemmas).
- C–E) Name/Type/Lex gates: measures and constructors are applied with explicit anchors to avoid elaboration ambiguity; lex decreases are branchwise checked.
- F) Stop-the-line: we do not assert global laws where a branch fails (e.g., local join for full Step).
- G) Probes P1–P3: see examples and comments inside Termination_KO7 for κ/μ branch splits and symbol availability.

These notes document the scope and design choices so the assessment items are fully addressed without changing the kernel or the SafeStep results.
