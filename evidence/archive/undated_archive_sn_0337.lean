import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination
import Init.WF
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Basic

open OperatorKernelO6
open Ordinal
open MetaSN  -- bring your mu-lemmas into scope

namespace OperatorKernelO6.MetaSNFinal

/-- primary depth-like counter; only `recΔ _ _ (delta _)` bumps by +1; everything else is a `max` -/
def kappaD : Trace → Nat
| .void                => 0
| .delta t             => kappaD t
| .integrate t         => kappaD t
| .merge a b           => Nat.max (kappaD a) (kappaD b)
| .recΔ b s (.delta n) => Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n) + 1
| .recΔ b s n          => Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n)
| .eqW a b             => Nat.max (kappaD a) (kappaD b)

@[simp] lemma kappaD_void : kappaD .void = 0 := rfl
@[simp] lemma kappaD_delta (t) : kappaD (.delta t) = kappaD t := rfl
@[simp] lemma kappaD_integrate (t) : kappaD (.integrate t) = kappaD t := rfl
@[simp] lemma kappaD_merge (a b) : kappaD (.merge a b) = Nat.max (kappaD a) (kappaD b) := rfl
@[simp] lemma kappaD_eqW (a b) : kappaD (.eqW a b) = Nat.max (kappaD a) (kappaD b) := rfl
@[simp] lemma kappaD_rec_succ (b s n) :
  kappaD (.recΔ b s (.delta n)) =
    Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n) + 1 := rfl
@[simp] lemma kappaD_rec_base (b s n) :
  kappaD (.recΔ b s n) =
    Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n) := by
  simp [kappaD]

/-- lex measure --/
noncomputable def muHat (t : Trace) : Nat × Ordinal := (kappaD t, MetaSN.mu t)

/-- lex order on (Nat × Ordinal) --/
def LexNatOrd : (Nat × Ordinal) → (Nat × Ordinal) → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- well-foundedness of lex product: Nat.< × Ordinal.< --/
lemma wf_LexNatOrd : WellFounded LexNatOrd := by
  -- std: `WellFounded.prod_lex` + `Nat.lt_wfRel.wf` + `Ordinal.lt_wf`
  exact WellFounded.prod_lex Nat.lt_wfRel.wf Ordinal.lt_wf
-- docs: lex product WF and ordinal WF are standard mathlib facts. :contentReference[oaicite:0]{index=0}

/-- helper: if κ decreases strictly, we drop left in lex --/
@[inline] lemma drop_left {a b : Trace}
  (hk : kappaD b < kappaD a) : LexNatOrd (muHat b) (muHat a) := by
  unfold LexNatOrd muHat; exact Prod.Lex.left _ _ hk

/-- helper: if κ is unchanged and μ decreases strictly, we drop right in lex --/
@[inline] lemma drop_right {a b : Trace}
  (hμ : MetaSN.mu b < MetaSN.mu a) (hk : kappaD b = kappaD a) :
  LexNatOrd (muHat b) (muHat a) := by
  unfold LexNatOrd muHat
  cases hk
  -- with equal first components: just use the `right` constructor
  simpa using (Prod.Lex.right (r₁ := (· < ·)) (r₂ := (· < ·)) hμ)

/-- κ strictly drops on `recΔ b s (delta n) → merge s (recΔ b s n)` --/
lemma kappaD_drop_recSucc (b s n : Trace) :
  kappaD (.merge s (.recΔ b s n)) < kappaD (.recΔ b s (.delta n)) := by
  -- let M be the big "max" on (b,s,n)
  let M := Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n)
  -- show `max (κ s) M = M`
  have hs_le_M : kappaD s ≤ M := by
    have : kappaD s ≤ Nat.max (kappaD b) (kappaD s) := Nat.le_max_right _ _
    exact Nat.le_trans this (Nat.le_max_left _ _)
  have hmax : Nat.max (kappaD s) M = M := Nat.max_eq_right hs_le_M
  -- LHS = M; RHS = M+1
  calc
    kappaD (.merge s (.recΔ b s n))
        = Nat.max (kappaD s) (kappaD (.recΔ b s n)) := by simp [kappaD]
    _   = Nat.max (kappaD s) M := by simp [kappaD_rec_base, kappaD, M]
    _   = M := by simpa [hmax]
    _   < M + 1 := Nat.lt_succ_self _
    _   = kappaD (.recΔ b s (.delta n)) := by simp [kappaD_rec_succ, kappaD, M]

/-- main: every kernel step strictly decreases the lex measure --/
lemma measure_drop_of_step :
  ∀ {a b : Trace}, Step a b → LexNatOrd (muHat b) (muHat a)
| _, _, Step.R_int_delta t =>
    -- integrate (delta t) → void
    by
      have hμ := MetaSN.mu_void_lt_integrate_delta t
      -- κ(source) = κ t; κ(target) = 0
      by_cases ht0 : kappaD t = 0
      · -- equal κ; use μ-drop
        have hk : kappaD (.void) = kappaD (.integrate (.delta t)) := by simp [kappaD, ht0]
        exact drop_right hμ hk
      · -- target κ < source κ
        have hk : kappaD (.void) < kappaD (.integrate (.delta t)) := by
          have : 0 < kappaD t := Nat.pos_of_ne_zero ht0
          simpa [kappaD] using this
        exact drop_left hk

| _, _, Step.R_merge_void_left t =>
    -- merge void t → t  (κ equal; μ drops)
    by
      have hμ := MetaSN.mu_lt_merge_void_left t
      have hk : kappaD t = kappaD (.merge .void t) := by simp [kappaD]
      exact drop_right hμ hk

| _, _, Step.R_merge_void_right t =>
    -- merge t void → t  (κ equal; μ drops)
    by
      have hμ := MetaSN.mu_lt_merge_void_right t
      have hk : kappaD t = kappaD (.merge t .void) := by simp [kappaD]
      exact drop_right hμ hk

| _, _, Step.R_merge_cancel t =>
    -- merge t t → t  (κ equal; μ drops)
    by
      have hμ := MetaSN.mu_lt_merge_cancel t
      have hk : kappaD t = kappaD (.merge t t) := by simp [kappaD]
      exact drop_right hμ hk

| _, _, Step.R_rec_zero b s =>
    -- recΔ b s void → b  (κ non-increasing; if strict, drop-left; else μ-drop)
    by
      have hμ := MetaSN.mu_lt_rec_base b s
      have hle : kappaD b ≤ kappaD (.recΔ b s .void) := by
        -- κ(rec b s void) = max (max κb κs) 0 = max κb κs ≥ κb
        simpa [kappaD] using (Nat.le_max_left (kappaD b) (kappaD s))
      by_cases hEq : kappaD b = kappaD (.recΔ b s .void)
      · exact drop_right hμ hEq
      · exact drop_left (Nat.lt_of_le_of_ne hle hEq)

| _, _, Step.R_rec_succ b s n =>
    -- recΔ b s (delta n) → merge s (recΔ b s n)  (κ drops by 1)
    by
      exact drop_left (kappaD_drop_recSucc b s n)

| _, _, Step.R_eq_refl a =>
    -- eqW a a → void  (if κ a > 0: drop-left; else equal κ and μ-drop)
    by
      have hμ := MetaSN.mu_void_lt_eq_refl a
      by_cases h0 : kappaD a = 0
      · have hk : kappaD (.void) = kappaD (.eqW a a) := by simp [kappaD, h0]
        exact drop_right hμ hk
      · have hk : kappaD (.void) < kappaD (.eqW a a) := by
          have : 0 < kappaD a := Nat.pos_of_ne_zero h0
          simpa [kappaD, Nat.max_self] using this
        exact drop_left hk

| a, b, Step.R_eq_diff hneq =>
    -- eqW a b → integrate (merge a b)  (κ equal; μ drops)
    by
      have hμ := MetaSN.mu_lt_eq_diff a b
      have hk : kappaD (.eqW a b) = kappaD (.integrate (.merge a b)) := by
        simp [kappaD, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
      exact drop_right hμ hk

/-- reverse relation for forward SN --/
def StepRev : Trace → Trace → Prop := fun a b => Step b a

/-- final SN: the reverse step relation is well-founded (no infinite forward reductions) --/
noncomputable theorem strong_normalization_final : WellFounded StepRev := by
  -- pull back WF of lex order along the measure `muHat`
  have wfMeasure : WellFounded (InvImage LexNatOrd muHat) :=
    InvImage.wf _ wf_LexNatOrd
  have sub : Subrelation StepRev (InvImage LexNatOrd muHat) := by
    intro a b h; exact measure_drop_of_step h
  exact Subrelation.wf sub wfMeasure

end OperatorKernelO6.MetaSNFinal



export MetaSN (strong_normalisation)
