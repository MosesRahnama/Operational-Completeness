# Termination - KO7 Lex3, MPO, and Hybrid Summary

This note consolidates the current termination strategy for the KO7-safe kernel and points to the audited lemmas in code. It mirrors the high-level document in `project_main_docs/Termination_Consolidation.md` and keeps a short, implementation-oriented index here.

- Canonical reference: `project_main_docs/Termination_Consolidation.md` (this Meta_md page is a concise pointer/summary).
- Code home: `OperatorKernelO6/Meta/Termination_KO7.lean` (KO7 Lex3 + MPO + Hybrid), plus `OperatorKernelO6/Meta/Termination.lean` for mu/mu-kappa tooling.

## KO7 triple measure (mu3) and Lex3

- Measure: mu3(t) = (delta(t), (kappaM(t), mu(t))) where:
  - delta(t) = 1 only for top-level `recΔ b s (delta n)`, else 0.
  - kappaM is a multiset of recursion weights (Dershowitz–Manna order).
  - mu is the ordinal measure used throughout MetaSN.
- Order: Lex3 = lexicographic on (Nat, Multiset-DM, Ordinal).
- Well-foundedness: by product-lex over wf(Nat<), wf(DM), wf(Ordinal<).

Audited KO7 drops (see `Meta/Termination_KO7.lean`):
- rec-succ: strict delta drop
  - `drop_R_rec_succ` — delta: 1 -> 0 (outer-left of Lex3).
- rec-zero: delta tie + kappaM strict drop
  - `drop_R_rec_zero` (requires delta(b)=0); kappaM strictly decreases for `recΔ b s void -> b`.
- integrate∘delta and void/merge helpers:
  - `drop_R_int_delta`, `drop_R_merge_void_left_zero`, `drop_R_merge_void_right_zero`.
- Restricted duplicates (mu-right under kappa=0 tie):
  - `drop_R_merge_cancel_zero`, `drop_R_eq_refl_zero`.

We package these into a guarded subrelation `SafeStep` and prove:
- `measure_decreases_safe` and `wf_SafeStepRev` (no infinite KO7-safe reductions).

## MPO mu-first for non-rec rules

- Size-like `sizeMPO` with mu-first lex on `(mu, (size, delta))`.
- All non-rec rules, plus eq/merge cases, strictly drop by mu-right:
  - `mpo_drop_R_int_delta`, `mpo_drop_R_merge_void_left/right`, `mpo_drop_R_merge_cancel`, `mpo_drop_R_eq_refl`, `mpo_drop_R_eq_diff`.
- Also `mpo_drop_R_rec_zero` (unguarded rec-zero via mu-only drop) for convenience.
- Guarded subrelation `SafeStepMPO` with `wf_SafeStepMPORev`.

## Hybrid certificates (per-step)

- `HybridDec a b := MPO-drop ∨ KO7-drop`.
- For every `Step a b`, `hybrid_drop_of_step h : HybridDec a b`.
- This isolates rule-by-rule decreases without forcing a single global measure across all rules.

## Notes and scope

- We intentionally do not require a mu-only unconditional drop for rec-succ; KO7 delta-first handles it cleanly.
- General merge-cancel/eq-refl without kappa=0 remain outside the KO7-safe aggregator (covered by MPO in HybridDec when needed).
- Aggregated "full Step" strong normalization is deferred until duplicate-heavy shapes are fully reconciled under one measure or guarded partitions.

## Quick index (code pointers)

- KO7 core: `Meta/Termination_KO7.lean`
  - DM setup and kappaM: section `MetaSN_DM`.
  - KO7 Lex3 + delta flag + drops: section `MetaSN_KO7` (drop lemmas, `SafeStep`, WF).
  - MPO mu-first (non-rec): section `MetaSN_MPO`.
  - Hybrid per-rule certs: section `MetaSN_Hybrid`.
- High-level doc: `project_main_docs/Termination_Consolidation.md`.

---
Last updated: sync with audited lemmas `drop_R_rec_succ`, `drop_R_rec_zero`, `drop_R_int_delta`, restricted `merge_cancel/eq_refl`, MPO suite, and HybridDec wrappers.
