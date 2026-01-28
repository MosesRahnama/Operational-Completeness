# Revised Tables Appendix (KO7 safe)

## Table R1 — KO7 Core Rules (code-accurate)
| ID | LHS | RHS | Orientation component used | Guards |
|---|---|---|---|---|
| R1 | merge void t | t | μ-right | δ(t)=0 (propagates) |
| R2 | merge t void | t | μ-right | δ(t)=0 (propagates) |
| R3 | merge t t | t | μ-right after tie | **SafeStep**: δ(t)=0 ∧ κ(t)=0 |
| R4 | recΔ b s void | b | κ-left (DM) | δ(b)=0 |
| R5 | recΔ b s (delta n) | app s (recΔ b s n) | **δ-left (1→0)** | none |
| R6 | integrate (delta t) | void | μ-right (κ rfl) | — |
| R7 | eqW a a | void | μ-right after tie | **SafeStep**: κ(a)=0 |
| R8 | eqW a b (a≠b) | integrate (merge a b) | μ-right | — |

## Table R2 — Per-rule decrease lemma names (paper ↔ code)
| Paper label | Code identifier | Notes |
|---|---|---|
| mpo_drop_R_eq_refl | drop_R_eq_refl_zero | μ-right, κ=0 guard |
| mpo_drop_R_eq_diff | drop_R_eq_diff | μ-right |
| mpo_drop_R_int_delta | drop_R_int_delta | μ-right; κ tie via kappaM_int_delta |
| dm_drop_R_rec_zero | dm_drop_R_rec_zero; drop_R_rec_zero | κ-left (DM) |
| drop_R_rec_succ | drop_R_rec_succ | δ-left |
| drop_R_merge_void_left/right_zero | drop_R_merge_void_left_zero; drop_R_merge_void_right_zero | μ-right |
| drop_R_merge_cancel_zero | drop_R_merge_cancel_zero | μ-right; guarded |

## Table R3 — δ-substitution checks
| Rule | Alias | Effect |
|---|---|---|
| rec_succ | delta_subst_drop_rec_succ | δ: 1→0 strict |
| rec_zero | delta_subst_drop_rec_zero | κ (DM) strict |

## Table R4 — Local-join lemmas (root) and context
| Peak form | Lemma(s) |
|---|---|
| integrate (delta t) | localJoin_int_delta |
| recΔ b s void | localJoin_rec_zero |
| recΔ b s (delta n) | localJoin_rec_succ |
| eqW a b (a≠b) | localJoin_eqW_ne |
| context lifting | localJoin_ctx_* |

## Table R5 — Normalizer and Newman
| Claim | Code name |
|---|---|
| Accessibility for recursion | acc_SafeStepRev |
| Packaged normalizer | normalizeSafePack |
| Normalizer function | normalizeSafe |
| Soundness certificates | to_norm_safe; norm_nf_safe |
| Existence of NF reachable | exists_nf_reachable |
| Confluence from SN+local-join | newman_safe |
| Uniqueness under local-join | normalizeSafe_*_of_loc |
