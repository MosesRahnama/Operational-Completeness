# Wrong Predictions and Simulated Failures (STRICT EXECUTION CONTRACT)

This index catalogs concrete places where prior AI reasoning went wrong (or relied on unsound/global claims), with file:line anchors and brief notes.

## Quick map (RP → RE → Sim → Fix)

| RP | Short description | RE | Simulation (section) | Primary fix anchor |
|---|---|---|---|---|
| RP-1 | Global rec_succ domination | RE-1 | Sim §5 (KO7 δ-flag P1), narrative | KO7 μ3 δ=1→0 (Termination_KO7) |
| RP-2 | κ equality at rec_succ | RE-2 | (branch-split narrative) | κ-drop or δ primary (SN/KO7) |
| RP-3 | Right-add strictness hazard | RE-3 | Sim §3 note | Guarded add/principal-add only |
| RP-4 | Duplication under additive measure | RE-4 | Sim §5 DM/μ mapping | DM on κᴹ; μ-right on tie |
| RP-6 | μ s vs μ(δ n) global comparison | RE-5 | Sim §4 counterexample | Avoid cross-parameter global bounds |

## RP-1: Global domination for rec_succ — not provable universally

Evidence (bound left as sorry):
```105:109:OperatorKernelO6/Legacy/Meta_Lean_Archive/Claude_SN.lean
-- Known problematic bound; left as sorry
have h_bound : omega0 ^ (MetaSN.mu (delta m) + MetaSN.mu s + (6 : Ordinal)) + omega0 * (MetaSN.mu b + 1) + 1 + 3 <
               (omega0 ^ (5 : Ordinal)) * (MetaSN.mu (delta m) + 1) + 1 + MetaSN.mu s + 6 := sorry
```
Parameterized workaround (sound):
```190:196:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_Legacy.lean
lemma mu_recΔ_plus_3_lt (b s n : Trace)
  (h_bound : omega0 ^ (mu n + mu s + (6 : Ordinal)) + omega0 * (mu b + 1) + 1 + 3 <
             (omega0 ^ (5 : Ordinal)) * (mu n + 1) + 1 + mu s + 6) :
  mu (recΔ b s n) + 3 < mu (delta n) + mu s + 6 := by
```

## RP-2: κ at rec_succ — equality mistakenly claimed

Equality (wrong):
```41:44:OperatorKernelO6/Legacy/Meta_Lean_Archive/Kappa.lean
@[simp] theorem kappa_eq_rec_succ (b s n : Trace) :
    kappa (merge s (recΔ b s n)) = kappa (recΔ b s (delta n)) := by
  simp only [kappa]
```
Strict drop (correct):
```954:958:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_C.lean
@[simp] lemma kappa_drop_recSucc (b s n : Trace) :
  kappa (merge s (recΔ b s n)) < kappa (recΔ b s (delta n)) := by
  simp [kappa]
```

## RP-3: Right-add strictness on ordinals — global transport is invalid

Hazard note in mainline:
```1571:1574:OperatorKernelO6/OperatorKernelO6/Meta/Termination.lean
-- aiming at μ n + μ s + 6 < μ (delta n) + μ s + 6 is invalid without extra hypotheses
```

## RP-4: Additive measure under duplication — fails without DM/MPO premise

Observation: additive assembly appears in legacy; strict drops require DM (each RHS piece < removed LHS) or μ/τ fallback when κᴹ ties.

## RP-5: Placeholder sorry/admit indicating wrong/incomplete predictions

```61:63:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_Lex.lean
intro _ _ _
sorry
```
```282:284:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN_Phi.lean
... ; admit
```
```77:79:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN_Delta.lean
... ; sorry
```

## RP-6: μ s vs μ (delta n) — global comparisons are false

Action: provide a concrete counterexample in simulations (planned).

## RP-7: φ (SN_Phi) mirrored rec_succ domination pattern

```206:213:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN_Phi.lean
/-- rec_succ: merge s (recΔ b s n) < recΔ b s (delta n). -/
-- Uses an A = ω^(E(δ n, s)) head and payload comparisons akin to μ-case
```
Key step references:
```227:243, 285:293:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN_Phi.lean
have bump : phi (recΔ b s n) + 3 < (omega0 ^ 5) * (phi (delta n) + 1) + phi s + 6 := ...
... A < A + ω*(φ b + 1) + 1
```

## RP-8: Legacy Termination variants repeat the pattern

```933:938:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination.lean
@[simp] lemma mu_lt_rec_succ (b s n : Trace) ... := by
  simpa using mu_merge_lt_rec h_mu_recΔ_bound
```
```939:951:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination.lean
lemma μκ_lt_R_rec_succ ... := by
  apply Prod.Lex.left; simp [kappa]
```

---

Planned simulations (build-safe):
- P1: Per-branch rfl failure for a pattern-matched function; corrected per-branch facts.
- P2: Duplication additive non-drop, then DM orientation premise.
- P3: Symbol realism (success + unknown id + arity mismatch) as comments or off-chain.
- Ordinal hazards: right-add counterexample; μ s > μ (delta n) instance.

See also: `OperatorKernelO6/Meta/ContractProbes.lean` and KO7/Computable measure files.

## RP-9: kappaTop attempts and commented sorry paths

Anchors:
```1562:1590:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_C.lean
-- kappaTop defined with ad-hoc values; μ_to_μκ_top relies on exact equality of first components
```
```1614:1672:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_C.lean
-- Multiple commented branches marked "impossible with kappaTop" and placeholder sorrys
```
```20:47:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_Lex.lean
-- kappaTop = 1 iff recΔ; μκTop pair; root-level only
```

## RP-10: MuLexSN (kappaTop, μ) path — temporary and narrow

Anchors:
```24:37, 52:76:OperatorKernelO6/Legacy/Meta_Lean_Archive/MuLexSN.lean
-- kappaTop primary + μ; rec_succ handled by left lex; other rules use μ-right
```

## RP-11: SN_Opus double-exponent μ₂ for rec_succ

Anchors:
```116:121, 178:180:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN_Opus.lean
-- μ₂ decrease for rec_succ; rec_zero/eq_refl integrate similarly
```

## RP-12: eq_refl and merge_cancel — μ-drop under κ tie

Anchors:
```977:984, 1000:1009:OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_C.lean
-- μκ_drop_R_eq_refl and μκ_drop_R_merge_cancel_nonrec: κ ties to 0, rely on μ-right
```

## RP-13: SN_Final — δ-flag primary for rec_succ

Anchors:
```11:14, 197:199:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN_Final.lean
@[simp] def deltaFlag : Trace → Nat
... rec_succ handled via flag drop (primary component)
```

## RP-14: SN — κD drop for rec_succ with μ-right ties

Anchors:
```27:33, 59:61, 79:81, 131:133:OperatorKernelO6/Legacy/Meta_Lean_Archive/SN.lean
-- kappaD_rec_succ; lex right when first components tie; κ drops at rec_succ
```

## RP-15: MuPort — “DOOMED APPROACH — DO NOT USE” (μ-only rec_succ)

Anchors:
```1:4, 28:30:OperatorKernelO6/Legacy/Meta_Lean_Archive/MuPort.lean
-- Explicitly warns not to attempt μ-only rec_succ proof via global rec_succ_bound
```

## RP-16: SafeStep scope — guarded decreases only (paper/code sync)

Anchors:
```11:26:Submission_Material/important/assessments_closure.md
-- Confluence_Safe proves local confluence and Newman for SafeStep only; guards are explicit.
```

## RP-17: Hybrid aggregator mentions vs code reality

Anchors:
```210:216, 300:305:Submission_Material/important/EXTRACTED_ISSUES_REPORT.md
-- Paper hints at hybrid decreases for full Step; code defers full aggregator and uses SafeStep/HybridDec per-rule only.
```
