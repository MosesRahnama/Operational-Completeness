# Paper ↔ Code cross‑reference

This map ties claims in the submission draft to concrete Lean lemmas/files.

- Strong normalization (safe relation)
  - Measure: `μ3`, `Lex3` in `OperatorKernelO6/Meta/Termination_KO7.lean`
  - Well-foundedness: `wf_SafeStepRev` (alias exported as `wf_StepRev_KO7_Safe`)
  - Per-rule decreases (samples):
    - `drop_R_merge_void_left_zero`, `drop_R_merge_void_right_zero`
    - `drop_R_rec_zero`, `drop_R_rec_succ`
    - `drop_R_merge_cancel_zero`

- Certified normalizer (safe)
  - Pack/def: `normalizeSafePack`, `normalizeSafe` in `OperatorKernelO6/Meta/Normalize_Safe.lean`
  - Properties: `to_norm_safe`, `norm_nf_safe`, `normalizeSafe_idempotent`

- Confluence via guarded Newman (safe)
  - Local joins at root: see `OperatorKernelO6/Meta/Confluence_Safe.lean` (e.g.,
    `localJoin_int_delta`, `localJoin_merge_tt`, `localJoin_rec_zero`, `localJoin_rec_succ`,
    `localJoin_eqW_ne`, plus guarded/vacuous variants)
  - Context lifting: `OperatorKernelO6/Meta/SafeStep_Ctx.lean` (`ctxstar_*`, `localJoin_*_ctx` wrappers)
  - Newman/star–star join + corollaries: `OperatorKernelO6/Meta/Newman_Safe.lean`

- Impossibility lemmas (failures of simple measures)
  - `kappa_plus_k_fails`, `simple_lex_fails` in `OperatorKernelO6/Meta/Impossibility_Lemmas.lean`

- Operational Incompleteness probes (P1–P3)
  - Branch rfl gate, duplication stress, DM/MPO witnesses: `OperatorKernelO6/Meta/Operational_Incompleteness_Skeleton.lean`

Notes
- For exact kernel rule names/shapes, see the Lean `Step` constructors in `OperatorKernelO6.lean` and use the per-rule drop lemmas in `Termination_KO7.lean`.
- Guarded local-join variants and ctx wrappers are documented inline in `Confluence_Safe.lean` and `SafeStep_Ctx.lean`.
