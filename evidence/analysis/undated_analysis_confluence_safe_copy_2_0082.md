# KO7‑Safe Local Confluence — Critical Peaks and Join Goals

Scope
- Relation: `MetaSN_KO7.SafeStep` (eight guarded root rules in `Termination_KO7.lean`).
- Goal: list root‑level critical overlaps (same redex unifying two rules) and state the join target for each. No proofs here; this is a checklist for a future `Confluence_Safe.lean`.

Notation
- `→ᵇ` denotes a single `SafeStep`.
- `⇒ᵇ*` denotes `SafeStepStar`.

Rules recap (names as constructors):
1. `R_int_delta t`:
   - `integrate (delta t) →ᵇ void`.
2. `R_merge_void_left t (hδ : deltaFlag t = 0)`:
   - `merge void t →ᵇ t`.
3. `R_merge_void_right t (hδ : deltaFlag t = 0)`:
   - `merge t void →ᵇ t`.
4. `R_merge_cancel t (hδ : deltaFlag t = 0) (h0 : kappaM t = 0)`:
   - `merge t t →ᵇ t`.
5. `R_rec_zero b s (hδ : deltaFlag b = 0)`:
   - `recΔ b s void →ᵇ b`.
6. `R_rec_succ b s n`:
   - `recΔ b s (delta n) →ᵇ app s (recΔ b s n)`.
7. `R_eq_refl a (h0 : kappaM a = 0)`:
   - `eqW a a →ᵇ void`.
8. `R_eq_diff a b`:
   - `eqW a b →ᵇ integrate (merge a b)`.

Root critical peaks (same LHS unifies two rules)

- Peak P1 — `eqW a a`:
  - Branches:
    - `eqW a a →ᵇ void` via `R_eq_refl` (requires `kappaM a = 0`).
    - `eqW a a →ᵇ integrate (merge a a)` via `R_eq_diff` (unguarded).
  - Join goal: exhibit `d` s.t. `void ⇒ᵇ* d` and `integrate (merge a a) ⇒ᵇ* d`.
   - Status: BLOCKER — still open. Related easy case solved separately: for `a ≠ b`, `eqW a b` has a unique root step (see `localJoin_eqW_ne`). If `kappaM a ≠ 0`, the `eqW a a` reflexive branch is blocked and the diff branch is unique (see `localJoin_eqW_refl_guard_ne`).

- Peak P2 — `merge void void` (when `deltaFlag void = 0`):
  - Branches:
    - `merge void void →ᵇ void` via `R_merge_void_left`.
    - `merge void void →ᵇ void` via `R_merge_void_right`.
    - If additionally `kappaM void = 0`, also `merge void void →ᵇ void` via `R_merge_cancel`.
  - Join goal: trivial (both sides already reduce to `void`).
   - Status: DONE — `localJoin_merge_void_void`.

- Peak P3 — `merge t t` with `t = void` (degenerate of P2 handled above):
  - Covered by P2 when guards hold; otherwise not a valid peak.

Non‑overlaps at root
- `R_int_delta` has no competing root rule on `integrate (delta t)` (proved: `localJoin_int_delta`).
- `R_rec_zero` vs `R_rec_succ` don’t unify (`void` vs `delta n`) (proved: `localJoin_rec_zero`, `localJoin_rec_succ`).
- `R_merge_void_left` vs `R_merge_void_right` apply to different patterns (covered by `localJoin_merge_void_left`, `localJoin_merge_void_right`, `localJoin_merge_tt`).

Out‑of‑root interactions
- If `SafeStep` is closed under contexts (not just root), additional peaks arise from overlapping at distinct positions. Those are not enumerated here; this checklist is strictly for root‑level overlaps between the eight guarded rules.

Join target heuristic (documentation only)
- When available, `MetaSN_KO7.normalizeSafe` provides a canonical join point: for any `x`, `x ⇒ᵇ* normalizeSafe x` and `normalizeSafe x` is safe‑normal.
- Formal join proofs must not rely on this heuristic; the local confluence layer should construct explicit `⇒ᵇ*` joins per peak (or invoke a proved Newman lemma once local confluence is shown).

Status
- Proven local-join lemmas in `Meta/Confluence_Safe.lean`:
   - Unique-step helpers: `localJoin_of_unique`, `localJoin_of_none`.
   - NF/bridge helpers: `localJoin_of_nf`, `localJoin_if_normalize_fixed`.
   - Trivial roots: `localJoin_merge_void_void`, `localJoin_int_delta`,
      `localJoin_merge_void_left`, `localJoin_merge_void_right`, `localJoin_merge_tt`,
      `localJoin_rec_zero`, `localJoin_rec_succ`.
   - Convenience: `localJoin_merge_void_delta`, `localJoin_merge_delta_void`, `localJoin_merge_delta_delta`.
    - More vacuous sources: `localJoin_void`, `localJoin_delta`, `localJoin_integrate_void`,
       `localJoin_integrate_merge`, `localJoin_integrate_app`, `localJoin_integrate_eqW`,
       `localJoin_integrate_integrate`, `localJoin_integrate_rec`.
   - eqW distinct: `localJoin_eqW_ne`.
   - Guard-negation vacuity: `localJoin_eqW_refl_guard_ne`,
      `localJoin_merge_void_left_guard_ne`, `localJoin_merge_void_right_guard_ne`,
      `localJoin_merge_cancel_guard_delta_ne`, `localJoin_merge_cancel_guard_kappa_ne`,
      `localJoin_rec_zero_guard_ne`.
- Open: P1 (`eqW a a`) remains the only non‑trivial peak. Until it is joined, `nfp_safe`, `global_confluence_safe`, and uniqueness remain deferred.

Context-closure addendum (in `Meta/SafeStep_Ctx.lean`)
- Defined `SafeStepCtx` (context-closure) and `SafeStepCtxStar` with lifting lemmas.
- Bridge and wrappers: `localJoin_ctx_of_localJoin` (embed root joins to ctx); wrappers for
   merge/no-void/neq and eqW distinct/reflex-guarded cases.
- Conditional eqW joins under ctx-star:
   - `localJoin_eqW_refl_ctx_if_merges_to_delta` (if `merge a a ⇒ctx* delta n`).
   - `ctxstar_merge_cancel_of_arg_to_delta` (from `a ⇒ctx* delta n` + guards to `merge a a ⇒ctx* delta n`).
   - `localJoin_eqW_refl_ctx_if_arg_merges_to_delta` (combines the above).
   - `localJoin_eqW_refl_ctx_if_merge_normalizes_to_delta` (if `normalizeSafe (merge a a) = delta n`).
   - `ctxstar_merge_cancel_of_arg_star_to_delta` (lift `a ⇒* delta n` to `merge a a ⇒ctx* delta n`).
   - Convenience: `localJoin_eqW_refl_ctx_when_a_is_delta`; `localJoin_eqW_refl_ctx_if_normalizes_to_delta`;
      `localJoin_eqW_refl_ctx_if_arg_star_to_delta` (root-star premise to delta).
   - Confluence wrappers: `localJoin_ctx_eqW_refl_if_merge_normalizes_to_delta`,
      `localJoin_ctx_eqW_refl_if_integrate_merge_to_void`,
   `localJoin_ctx_eqW_refl_if_merges_to_delta`,
   `localJoin_ctx_eqW_refl_if_arg_merges_to_delta`,
      `localJoin_ctx_eqW_refl_if_arg_star_to_delta`,
      `localJoin_ctx_eqW_refl_if_normalizes_to_delta`,
      `localJoin_ctx_eqW_refl_when_a_is_delta`.
   - Vacuities mirrored in ctx: `localJoin_ctx_void`, `localJoin_ctx_delta`, `localJoin_ctx_app`,
      `localJoin_ctx_integrate_void`, `localJoin_ctx_integrate_merge`, `localJoin_ctx_integrate_app`,
      `localJoin_ctx_integrate_eqW`, `localJoin_ctx_integrate_integrate`, `localJoin_ctx_integrate_rec`,
      `localJoin_ctx_rec_merge`, `localJoin_ctx_rec_app`, `localJoin_ctx_rec_integrate`, `localJoin_ctx_rec_eqW`.
   - Root-unique cases mirrored in ctx: `localJoin_ctx_rec_zero`, `localJoin_ctx_rec_succ`,
      `localJoin_ctx_merge_void_left`, `localJoin_ctx_merge_void_right`, `localJoin_ctx_merge_tt`,
      `localJoin_ctx_int_delta`.
   - Convenience (ctx): `localJoin_ctx_merge_void_void`, `localJoin_ctx_merge_void_delta`,
      `localJoin_ctx_merge_delta_void`, `localJoin_ctx_merge_delta_delta`.
