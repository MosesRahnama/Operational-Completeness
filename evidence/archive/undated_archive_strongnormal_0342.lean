/-
  OperatorKernelO6/Meta/SN_Final.lean
  Slim SN proof via (κ, μ) lexicographic measure.

  κ := kappaD from Termination_Lex (with +2 at recΔ _ _ (delta _)).
  μ := MetaSN.mu from Termination (and its μ-decrease lemmas).
-/
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination        -- provides MetaSN.mu and μ-lemmas
import OperatorKernelO6.Meta.Termination_Lex    -- provides kappaD and kappaD_drop_recSucc
import Init.WF
import Mathlib.Data.Prod.Lex
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open OperatorKernelO6 Trace Ordinal Nat MetaSN
open OperatorKernelO6.MetaSNFinal  -- brings kappaD, kappaD_drop_recSucc, LexNatOrd pattern

namespace SN

/-- Primary counter κ (alias of the working `kappaD`). -/
def kappa : Trace → Nat := OperatorKernelO6.MetaSNFinal.kappaD

@[simp] lemma kappa_void : kappa void = 0 := rfl
@[simp] lemma kappa_delta (t) : kappa (delta t) = kappa t := rfl
@[simp] lemma kappa_integrate (t) : kappa (integrate t) = kappa t := rfl
@[simp] lemma kappa_merge (a b) : kappa (merge a b) = Nat.max (kappa a) (kappa b) := rfl
@[simp] lemma kappa_eqW (a b) : kappa (eqW a b) = Nat.max (kappa a) (kappa b) := rfl
@[simp] lemma kappa_rec_succ (b s n) :
  kappa (recΔ b s (delta n)) =
    Nat.max (Nat.max (kappa b) (kappa s)) (kappa n) + 2 := rfl
@[simp] lemma kappa_rec_base (b s n) :
  kappa (recΔ b s n) =
    Nat.max (Nat.max (kappa b) (kappa s)) (kappa n) := by
  cases n <;> simp [kappa]

/-- Combined lexicographic measure (κ, μ). -/
noncomputable def measure (t : Trace) : Nat × Ordinal := (kappa t, MetaSN.mu t)

/-- Lex on `(Nat × Ordinal)`. -/
def LexOrder : (Nat × Ordinal) → (Nat × Ordinal) → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- Well-foundedness of the lex order. -/
lemma wf_LexOrder : WellFounded LexOrder :=
  WellFounded.prod_lex Nat.lt_wfRel.wf Ordinal.lt_wf

@[simp] lemma kappa_rec_base  (b s n) :
  kappa (recΔ b s n) = Nat.max (Nat.max (kappa b) (kappa s)) (kappa n)

@[simp] lemma kappa_rec_succ  (b s n) :
  kappa (recΔ b s (delta n)) = Nat.max (Nat.max (kappa b) (kappa s)) (kappa n) + 2

/-- Left-branch drop helper. -/
@[inline] lemma drop_left {a b : Trace} (hk : kappa b < kappa a) :
    LexOrder (measure b) (measure a) :=
  Prod.Lex.left _ _ hk

/-- Right-branch drop helper (κ equal, μ drops). -/
@[inline] lemma drop_right {a b : Trace}
    (hμ : MetaSN.mu b < MetaSN.mu a) (hk : kappa b = kappa a) :
    LexOrder (measure b) (measure a) := by
  unfold LexOrder measure
  simpa [hk] using Prod.Lex.right _ hμ

/-- κ strictly drops for `R_rec_succ` (imported pattern). -/
@[inline] lemma kappa_drop_recSucc (b s n : Trace) :
    kappa (merge s (recΔ b s n)) < kappa (recΔ b s (delta n)) := by
  -- definally identical to the lemma in `Termination_Lex.lean`
  simpa using OperatorKernelO6.MetaSNFinal.kappaD_drop_recSucc b s n

open OperatorKernelO6.Step

/-- Every primitive step strictly decreases the lexicographic measure. -/
theorem measure_decreases : ∀ {a b : Trace}, Step a b → LexOrder (measure b) (measure a)
| _, _, R_int_delta t =>
    -- κ equal; use μ(void) < μ(integrate (delta t))
    drop_right (MetaSN.mu_void_lt_integrate_delta t) (by simp [measure, kappa])
| _, _, R_merge_void_left t =>
    drop_right (MetaSN.mu_lt_merge_void_left t) (by simp [kappa])
| _, _, R_merge_void_right t =>
    drop_right (MetaSN.mu_lt_merge_void_right t) (by simp [kappa])
| _, _, R_merge_cancel t =>
    drop_right (MetaSN.mu_lt_merge_cancel t) (by simp [kappa])
| _, _, R_rec_zero b s =>
    -- κ(b) ≤ κ(recΔ b s void); if equal, use μ-drop; else κ-drop
    by
      have hb_le : kappa b ≤ kappa (recΔ b s void) := by
        have h1 : kappa b ≤ Nat.max (kappa b) (kappa s) := Nat.le_max_left _ _
        have h2 : Nat.max (kappa b) (kappa s) ≤
                  Nat.max (Nat.max (kappa b) (kappa s)) (kappa void) := Nat.le_max_left _ _
        simpa [kappa] using le_trans h1 h2
      by_cases hb_eq : kappa b = kappa (recΔ b s void)
      · exact drop_right (MetaSN.mu_lt_rec_zero b s) hb_eq
      · exact drop_left (Nat.lt_of_le_of_ne hb_le hb_eq)
| _, _, R_rec_succ b s n =>
    -- single line: κ strictly drops for successor step
    drop_left (kappa_drop_recSucc b s n)
| _, _, R_eq_refl a =>
    -- κ equal (to max κ a κ a); μ(void) < μ(eqW a a)
    drop_right (MetaSN.mu_void_lt_eq_refl a) (by simp [kappa])
| _, _, R_eq_diff (a:=a) (b:=b) hneq =>
    -- κ equal; μ strictly drops via the eq-diff lemma
    drop_right (MetaSN.mu_lt_eq_diff a b) (by simp [kappa])

/-- Reverse relation for forward normalization. -/
def StepRev : Trace → Trace → Prop := fun a b => Step b a

/-- Strong normalization: well-foundedness of `StepRev`. -/
theorem strong_normalization : WellFounded StepRev := by
  have wf_measure : WellFounded (InvImage LexOrder measure) :=
    InvImage.wf _ wf_LexOrder
  have sub : Subrelation StepRev (InvImage LexOrder measure) := by
    intro a b hab; exact measure_decreases hab
  exact Subrelation.wf sub wf_measure

/-- Acc form (pointwise). -/
theorem strong_normalization' (t : Trace) : Acc StepRev t :=
  strong_normalization.apply t

end SN
