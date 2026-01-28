# Hybrid Termination Artifacts (KO7 + MPO)

This note summarizes the publishable termination artifacts consolidated in `OperatorKernelO6/Meta/Termination_KO7.lean`.

Scope and claims:
- Per-step hybrid decrease: every `Kernel.Step a b` strictly decreases either the MPO-style measure `ν3m` (μ-first) or the KO7 triple-lex measure `μ3`.
  - Formal: `MetaSN_Hybrid.hybrid_drop_of_step : Step a b → HybridDec a b`.
- Safe subrelations are well-founded in reverse:
  - KO7-safe: `MetaSN_KO7.wf_SafeStepRev : WellFounded MetaSN_KO7.SafeStepRev`.
  - MPO-safe: `MetaSN_MPO.wf_SafeStepMPORev : WellFounded MetaSN_MPO.SafeStepMPORev`.
- We do not assert a single global measure over the entire `Step` due to duplication and right-add hazards (ordinal addition). Instead, we expose the hybrid certificate and two safe well-founded subsets. This is intentional and documented.

Key definitions and lemmas (Lean names):
- KO7 triple measure and order:
  - `MetaSN_KO7.deltaFlag : Trace → Nat`
  - `MetaSN_KO7.μ3 : Trace → Nat × (Multiset ℕ × Ordinal)`
  - `MetaSN_KO7.Lex3` and `MetaSN_KO7.wf_Lex3`
- MPO measure and order:
  - `MetaSN_MPO.sizeMPO : Trace → Nat`
  - `MetaSN_MPO.ν3m : Trace → Ordinal × (Nat × Nat)`
  - `MetaSN_MPO.LexNu3m` and `MetaSN_MPO.wf_LexNu3m`
- Hybrid certificate and public wrappers:
  - `MetaSN_Hybrid.HybridDec`
  - `MetaSN_Hybrid.hybrid_drop_of_step`
  - `wf_StepRev_KO7_Safe`, `wf_StepRev_MPO_Safe`

Practical usage:
- For any single reduction step `h : Step a b`, call `hybrid_drop_of_step h` to obtain a strict measure decrease (either branch).
- For termination (no infinite reductions) of constrained strategies:
  - Use `wf_StepRev_KO7_Safe` when your sequence respects KO7-side guards (δ-ties and κ-side conditions stated in `SafeStep`).
  - Use `wf_StepRev_MPO_Safe` for non-recursive rule closures and base recursion (`rec_zero`).

Notes on design choices:
- Right-addition of ordinals is not strictly monotone; our proofs avoid transporting `<` through `… + c` on the right without explicit hypotheses. Where additive-principal folding is used, we first justify the required bounds (e.g., `omega0 ≤ p`).
- κ-duplication (e.g., `merge_cancel`, `eq_refl`) is handled by μ-first MPO lemmas; KO7 κ-first is used where structurally safe.

Citing these results:
- “Per-step hybrid decrease” — `MetaSN_Hybrid.hybrid_drop_of_step`.
- “Safe KO7 termination” — `MetaSN_KO7.wf_SafeStepRev` (or the public alias `wf_StepRev_KO7_Safe`).
- “Safe MPO termination” — `MetaSN_MPO.wf_SafeStepMPORev` (or the public alias `wf_StepRev_MPO_Safe`).

Status: build green on branch `guide/consolidated-ssot` as of 2025-08-16.

## Examples (Lean)

```lean
import OperatorKernelO6

open OperatorKernelO6

-- Per-step hybrid certificate
example {a b : Trace} (h : Step a b) : MetaSN_Hybrid.HybridDec a b :=
  MetaSN_Hybrid.hybrid_drop_of_step h

-- KO7-safe subrelation is well-founded (reverse)
#check MetaSN_KO7.wf_SafeStepRev
#check wf_StepRev_KO7_Safe   -- public alias

-- MPO-safe subrelation is well-founded (reverse)
#check MetaSN_MPO.wf_SafeStepMPORev
#check wf_StepRev_MPO_Safe   -- public alias
```
