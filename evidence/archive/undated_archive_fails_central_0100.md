# Central Consolidation — Failure Modes and Corrections (OperatorKernelO6)

Last updated: 2025-08-17

Scope
- Consolidates: `fails.md`, `fails_2.md`, `fails_3.md`, `o3_fails_consolidated.md`, `opus_fails_consolidated.md`, and `Termination_Consolidation.md`.
- Enforces the STRICT EXECUTION CONTRACT gates P1–P3 with explicit minimal counterexamples and exact code anchors.

How to read
- For each claim, we show: the original statement (with source), branch-by-branch rfl checks or counterexample (P1), the duplication stress identity (P2), and the corrective principle with current Lean lemma anchors (KO7/MPO/Hybrid).

---
## A. The single hard rule (all sources agree)

Rule
  R_rec_succ: recΔ b s (δ n) → merge s (recΔ b s n)

Why hard
- Duplicates `s` on RHS; `n` may be δ-shaped, causing ties for shape-blind measures.

Corrective anchor
- KO7 delta-first drop: `Meta/Termination_KO7.lean` — lemma `drop_R_rec_succ` (outer deltaFlag 1→0).

---
## B. Pure ordinal μ-only decreases (rec_succ_bound)

Claim (fails.md §1; fails_2.md §1)
- “μ decreases on every rule, including rec_succ” via a bound rec_succ_bound.

P1 Branch-by-branch
- Global equation μ(LHS) > μ(RHS) cannot be closed uniformly; any proof uses a hidden false inequality.

P2 Duplication stress
- Not applicable directly; issue is domination, not additivity. Ordinal right-add/absorption pitfalls recur.

Counterexample
- When n nests δ arbitrarily and s carries large μ mass, no uniform bound proves μ(recΔ b s (δ n)) > μ(merge s (recΔ b s n)).

Corrective principle
- Avoid global μ domination for rec_succ. Use KO7’s delta-first Lex3: `drop_R_rec_succ`.

---
## C. κ = max-depth + k (k = 1,2,…) constant bumps

Claim (fails.md §§2–3; fails_2.md §§2–3)
- “Add +k on δ-case to force strictness.”

P1 rfl per-branch
- For n = δ m, κ(recΔ … n) = base + k ties both sides; no strict drop.

P2 Duplication stress identity
- Not the primary mechanism; the tie arises before considering duplication.

Minimal counterexample
- Take n = δ m. Then κ(merge s (recΔ b s n)) = max(κ s, base+k) = base+k = κ(recΔ b s (δ n)).

Corrective principle
- Replace scalar bump with structural flag that strictly drops on rec_succ: KO7 `deltaFlag` outer component with Lex3 ordering.

Anchors
- `Meta/Termination_KO7.lean`: `drop_R_rec_succ`; Lex3 defined around μ3/deltaFlag.

---
## D. (κ, μ) lex where μ “handles ties”

Claim (fails.md §4)
- When κ ties, μ will strictly decrease.

P1 check
- This re-imports the false μ-bound (rec_succ_bound). The problematic inequality is unchanged.

Corrective principle
- Do not delegate rec_succ to μ. Use KO7’s outer delta drop; keep μ for other rules or inside Hybrid/MPO.

Anchors
- `Meta/Termination_KO7.lean`: `drop_R_rec_succ`; `measure_decreases_safe` aggregates safe rules.

---
## E. κ(+2) with helper inequalities

Claim (fails.md §5; fails_3.md §6)
- Attempt to prove κ(recΔ … n) ≤ base+1 and < base+2.

P1 per-branch rfl
- In the n = δ _ branch, κ(recΔ … n) = base+1 already, so ≤ base+1 holds as equality, but the RHS after step also attains base+1; strictness still fails.

Corrective principle
- Same as C/D: abandon constant offsets; use KO7 delta-first.

---
## F. Boolean δ-flag alone (0/1) as outer discriminator

Claim (fails.md §6; fails_3.md §7)
- Use a binary flag for top-form recΔ … (δ _).

P1 branch realism
- Some non-rec rules can increase the flag (e.g., merge void t when t is “bad”), breaking lex monotonicity.

Corrective principle
- In KO7, the deltaFlag is used only in a guarded subrelation where side rules preserve tie hypotheses (e.g., with hδ : deltaFlag t = 0). Do not use an unguarded global flag.

Anchors
- `drop_R_merge_void_left_zero`, `drop_R_merge_void_right_zero` require hδ = 0; `measure_decreases_safe` aggregates these guarded cases.

---
## G. ρ counter = count of bad nodes

Claim (fails.md §7; fails_3.md §8)
- Count recΔ _ _ (δ _) nodes; expect -1 on rec_succ.

P2 duplication stress identity (explicit)
- From `OpIncomp.P2.dup_additive_failure` style reasoning: count(after) = count(before) - 1 + count(s). If count(s) ≥ 1, no strict drop.

Corrective principle
- Use DM multiset or MPO so duplication is safe by construction.

Anchors
- `OpIncomp.P2` theorems `dup_additive_failure`, `not_strict_drop` (toy calculus); DM/MPO orientation witnesses in `OpIncomp.P2DM.dm_orient_dup` and `OpIncomp.P2MPO.mpo_orient_dup`.

---
## H. Quick inequality patching (replace = by ≤)

Claim (fails_3.md §11)
- Swap equalities for inequalities to escape False goals.

P1/P2
- The same nested-δ counterexample defeats the patched inequalities.

Corrective principle
- Switch to structural orders (KO7/MPO) rather than arithmetic slack.

---
## I. Contract gates P1–P3 (explicit probes)

P1 Branch realism (NameGate)
- Two-clause function f with per-branch rfl; global law fails at x=1. Source: `OpIncomp.P1` examples.

P2 Duplication realism
- Additive non-drop identity and strict-drop impossibility under size; DM/MPO fixes with concrete witnesses. Source: `OpIncomp.P2`, `P2DM`, `P2MPO`.

P3 Symbol realism
- Success: `#check P2.size`. Unknown identifier and arity/type mismatch kept commented to preserve green build. Source: `OpIncomp.P3`.

---
## J. Current green path summary (cross-check with Termination_Consolidation)

KO7 Lex3 (delta, κM-DM, μ)
- `drop_R_rec_succ` (strict delta drop), `drop_R_rec_zero` (κM drop under δ-tie), `drop_R_int_delta`, restricted `drop_R_merge_cancel_zero`/`drop_R_eq_refl_zero` (μ-right under κ=0).
- Aggregation: `measure_decreases_safe`, `wf_SafeStepRev`.

MPO μ-first (non-rec rules)
- `SafeStepMPO` suite and `wf_SafeStepMPORev`.

Hybrid per-step certificates
- `HybridDec` and `hybrid_*` lemmas, plus `hybrid_drop_of_step` (examples at end of KO7 file).

Confluence and normalization (guarded)
- Newman engine at source: `Meta/Newman_Safe.lean` (`join_star_star`, `newman_safe`).
- Normalizer: `Meta/Normalize_Safe.lean` (`normalizeSafe`, `to_norm_safe`).

---
## K. Early-warning checklist (operationalised)

- Always test n = δ m for any κ-variant; if it ties, abandon.
- Inspect duplication: any additive counter must fail if a rule duplicates subterms carrying the bad shape.
- For ordinals: never use right-add or absorption without explicit hypotheses (`omega0 ≤ p`).
- Treat any `sorry` in a core inequality as a blocker; switch to structural orders.

---
## L. Minimal counterexamples (ready-to-use)

- κ+k tie: pick n = δ m. Both sides evaluate to base + k.
- ρ counter: pick s with at least one bad node; net change ≥ 0 by -1 + ρ(s).
- μ domination: choose s large and n nested; no uniform μ bound exists without false arithmetic.

---
## M. Appendix — Exact code anchors

- KO7: `OperatorKernelO6/Meta/Termination_KO7.lean`
  - Lines ~200–380: `drop_R_int_delta`, `drop_R_rec_succ`, `drop_R_rec_zero`, restricted `drop_R_merge_cancel_zero`, `drop_R_eq_refl_zero`, `measure_decreases_safe`, `wf_SafeStepRev`.
  - Lines ~520–620: `SafeStepMPO`, `mpo_measure_decreases`, `wf_SafeStepMPORev`.
  - Lines ~730–770: `lex3_drop_*` wrapper lemmas.
- Newman: `OperatorKernelO6/Meta/Newman_Safe.lean` — `join_star_star`, `newman_safe`, normalization corollaries.
- Normalizer: `OperatorKernelO6/Meta/Normalize_Safe.lean` — `normalizeSafePack`, `to_norm_safe`.
- Operational skeleton: `OperatorKernelO6/Meta/Operational_Incompleteness_Skeleton.lean` — P1/P2/P2DM/P2MPO/P3.

End of file.
