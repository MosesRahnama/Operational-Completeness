import OperatorKernelO6.Meta.Normalize_Safe

open Classical
open OperatorKernelO6 Trace

namespace MetaSN_KO7

/-- Bundled soundness of the KO7 safe normalizer. -/
theorem normalizeSafe_sound (t : Trace) :
  SafeStepStar t (normalizeSafe t) ∧ NormalFormSafe (normalizeSafe t) :=
  ⟨to_norm_safe t, norm_nf_safe t⟩

/-- Totality alias for convenience: every trace safely normalizes to some NF. -/
theorem normalizeSafe_total (t : Trace) :
  ∃ n, SafeStepStar t n ∧ NormalFormSafe n :=
  ⟨normalizeSafe t, to_norm_safe t, norm_nf_safe t⟩

end MetaSN_KO7
