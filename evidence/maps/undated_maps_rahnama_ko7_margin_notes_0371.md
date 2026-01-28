# Red-pen margin notes for Rahnama_KO7.pdf

## 1. Fix rec-succ rule (remove duplication, add app)
**Seen on pages:** 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11

**Replace:**

> rec b s (succ n) → step (rec b s n) (rec b s n)

**With:**

> recΔ b s (delta n) → app s (recΔ b s n)

**Comment:** Code does not duplicate RHS; strict decrease is δ-phase (1→0). Adjust orientation discussion accordingly.

## 2. Guard explicit: merge-cancel
**Seen on pages:** 2, 3, 5, 6, 9, 10, 11

**Replace:**

> merge t t → t

**With:**

> merge t t → t   (SafeStep guard: δ(t)=0 ∧ κ(t)=0)

**Comment:** Paper must state SafeStep guard; μ-right handles the tie after guard.

## 3. Guard explicit: eqW reflexive
**Seen on pages:** 1, 2, 3, 4, 5, 9, 10, 11

**Replace:**

> eqW a a → void

**With:**

> eqW a a → void   (SafeStep guard: κ(a)=0)

**Comment:** State κ=0 guard; μ-right orientation gives strict drop under guard.

## 4. Rename per-rule lemmas to code identifiers
**Seen on pages:** (could not auto-detect; refer to rules table / corresponding section)

**Replace:**

> mpo_drop_R_eq_refl, mpo_drop_R_eq_diff, mpo_drop_R_int_delta

**With:**

> drop_R_eq_refl_zero, drop_R_eq_diff, drop_R_int_delta (plus kappaM_int_delta rfl)

**Comment:** Use code-accurate names; these are what `measure_decreases_safe` invokes.

## 5. δ-substitution aliases
**Seen on pages:** 2, 5, 6, 9, 10, 11

**Replace:**

> (not listed)

**With:**

> delta_subst_drop_rec_succ; delta_subst_drop_rec_zero

**Comment:** List these explicitly to pass the δ-substitution checklist in the text.

## 6. Local-join lemma names
**Seen on pages:** 1, 2, 4, 5, 7, 8, 9, 10, 11, 12

**Replace:**

> Generic references to local confluence

**With:**

> localJoin_int_delta; localJoin_rec_zero; localJoin_rec_succ; localJoin_eqW_ne; localJoin_ctx_*

**Comment:** Match the code’s concrete lemma names in the tables.

## 7. Newman bridge + normalizer corollaries
**Seen on pages:** 1, 2, 4, 5, 7, 8, 9, 11

**Replace:**

> By Newman, we get confluence and canonical normal forms.

**With:**

> newman_safe; normalizeSafe_unique_of_loc; normalizeSafe_eq_of_star_of_loc

**Comment:** Cite exact identifiers used in the artifact.

