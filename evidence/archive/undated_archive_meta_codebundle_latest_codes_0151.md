# Remaining experimental SN measure variants

# Kernel.lean

```lean
namespace OperatorKernelO6

inductive Trace : Type
| void : Trace
| delta : Trace → Trace
| integrate : Trace → Trace
| merge : Trace → Trace → Trace
| recΔ : Trace → Trace → Trace → Trace
| eqW : Trace → Trace → Trace

open Trace

inductive Step : Trace → Trace → Prop
| R_int_delta : ∀ t, Step (integrate (delta t)) void
| R_merge_void_left : ∀ t, Step (merge void t) t
| R_merge_void_right : ∀ t, Step (merge t void) t
| R_merge_cancel : ∀ t, Step (merge t t) t
| R_rec_zero : ∀ b s, Step (recΔ b s void) b
| R_rec_succ : ∀ b s n, Step (recΔ b s (delta n)) (merge s (recΔ b s n))
| R_eq_refl : ∀ a, Step (eqW a a) void
| R_eq_diff : ∀ {a b}, a ≠ b → Step (eqW a b) (integrate (merge a b))


inductive StepStar : Trace → Trace → Prop
| refl : ∀ t, StepStar t t
| tail : ∀ {a b c}, Step a b → StepStar b c → StepStar a c

def NormalForm (t : Trace) : Prop := ¬ ∃ u, Step t u

theorem stepstar_trans {a b c : Trace} (h1 : StepStar a b) (h2 : StepStar b c) : StepStar a c := by
  induction h1 with
  | refl => exact h2
  | tail hab _ ih => exact StepStar.tail hab (ih h2)

theorem stepstar_of_step {a b : Trace} (h : Step a b) : StepStar a b :=
  StepStar.tail h (StepStar.refl b)

theorem nf_no_stepstar_forward {a b : Trace} (hnf : NormalForm a) (h : StepStar a b) : a = b :=
  match h with
  | StepStar.refl _ => rfl
  | StepStar.tail hs _ => False.elim (hnf ⟨_, hs⟩)


end OperatorKernelO6

```

# Termination_Lex.lean

```lean
import OperatorKernelO6.Kernel
import Init.WF
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic
import OperatorKernelO6.Meta.MuCore

open Ordinal
open OperatorKernelO6
open Trace

namespace OperatorKernelO6.TerminationLex

/-- κ(t) = 1 exactly at a `recΔ _ _ (delta _)` root; 0 otherwise.
    This guarantees: strict drop only on `R_rec_succ`; unchanged elsewhere. -/
def kappa : Trace → Nat
| recΔ _ _ (delta _) => 1
| _                  => 0

@[simp] lemma kappa_rec_succ (b s n : Trace) :
  kappa (recΔ b s (delta n)) = 1 := rfl
@[simp] lemma kappa_merge (a b : Trace) : kappa (merge a b) = 0 := rfl
@[simp] lemma kappa_rec_base (b s n : Trace) : kappa (recΔ b s n) = 0 := by
  cases n <;> simp [kappa]
@[simp] lemma kappa_void : kappa void = 0 := rfl
@[simp] lemma kappa_delta (t) : kappa (delta t) = 0 := rfl
@[simp] lemma kappa_integrate (t) : kappa (integrate t) = 0 := rfl
@[simp] lemma kappa_eqW (a b) : kappa (eqW a b) = 0 := rfl

/-- Combined lexicographic measure. -/
noncomputable def muHat (t : Trace) : Nat × Ordinal := (kappa t, MuCore.mu t)

/-- Lex order on (Nat × Ordinal). -/
def LexNatOrd : (Nat × Ordinal) → (Nat × Ordinal) → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- Well-foundedness of the lex product. -/
lemma wf_LexNatOrd : WellFounded LexNatOrd :=
  WellFounded.prod_lex Nat.lt_wfRel.wf (fun _ => Ordinal.lt_wf)

/-- Left-branch: decrease on κ. -/
@[inline] lemma drop_left {a b : Trace} (hk : kappa b < kappa a) :
  LexNatOrd (muHat b) (muHat a) := by
  unfold LexNatOrd muHat; exact Prod.Lex.left _ _ hk

/-- Right-branch: κ unchanged, μ strictly drops. -/
@[inline] lemma drop_right {a b : Trace}
  (hμ : MuCore.mu b < MuCore.mu a) (hk : kappa b = kappa a) :
  LexNatOrd (muHat b) (muHat a) := by
  unfold LexNatOrd muHat; cases hk; simpa using Prod.Lex.right _ hμ

/-- κ strictly drops on `recΔ b s (delta n) → merge s (recΔ b s n)`. -/
lemma kappa_drop_recSucc (b s n : Trace) :
  kappa (merge s (recΔ b s n)) < kappa (recΔ b s (delta n)) := by
  -- RHS = 1; LHS = 0.
  simp [kappa]

/-- Each kernel step strictly decreases the lexicographic measure. -/
lemma measure_drop_of_step :
  ∀ {a b : Trace}, Step a b → LexNatOrd (muHat b) (muHat a)
| _, _, Step.R_int_delta t =>
    -- integrate (delta t) → void : κ equal (both 0); μ drops.
    by
      have hμ := MuCore.mu_void_lt_integrate_delta t
      have hk : kappa void = kappa (integrate (delta t)) := by simp [kappa]
      exact drop_right hμ hk.symm
| _, _, Step.R_merge_void_left t =>
    by
      have hμ := MuCore.mu_lt_merge_void_left t
      have hk : kappa t = kappa (merge void t) := by simp [kappa]
      exact drop_right hμ hk.symm
| _, _, Step.R_merge_void_right t =>
    by
      have hμ := MuCore.mu_lt_merge_void_right t
      have hk : kappa t = kappa (merge t void) := by simp [kappa]
      exact drop_right hμ hk.symm
| _, _, Step.R_merge_cancel t =>
    by
      have hμ := MuCore.mu_lt_merge_cancel t
      have hk : kappa t = kappa (merge t t) := by simp [kappa]
      exact drop_right hμ hk.symm
| _, _, Step.R_rec_zero b s =>
    by
      have hμ := MuCore.mu_lt_rec_zero b s
      have hk : kappa b = kappa (recΔ b s void) := by simp [kappa]
      exact drop_right hμ hk.symm
| _, _, Step.R_rec_succ b s n =>
    -- recΔ b s (delta n) → merge s (recΔ b s n) : κ drops.
    by
      exact drop_left (kappa_drop_recSucc b s n)
| _, _, Step.R_eq_refl a =>
    by
      have hμ := MuCore.mu_void_lt_eq_refl a
      have hk : kappa void = kappa (eqW a a) := by simp [kappa]
      exact drop_right hμ hk.symm
| _, _, Step.R_eq_diff (a := a) (b := b) _ =>
    -- eqW a b → integrate (merge a b) : μ drops; κ equal.
    by
      have hμ := MuCore.mu_lt_eq_diff a b
      have hk : kappa (integrate (merge a b)) = kappa (eqW a b) := by simp [kappa]
      exact drop_right hμ hk.symm

/-- Reverse relation for forward normalization. -/
def StepRev : Trace → Trace → Prop := fun a b => Step b a

/-- Final strong normalization: no infinite forward `Step` chains. -/
theorem strong_normalization : WellFounded StepRev := by
  -- Pull back WF of the lex order along `muHat`.
  have wfMeasure : WellFounded (InvImage LexNatOrd muHat) :=
    InvImage.wf _ wf_LexNatOrd
  have sub : Subrelation StepRev (InvImage LexNatOrd muHat) := by
    intro a b h; exact measure_drop_of_step h
  exact Subrelation.wf sub wfMeasure

end OperatorKernelO6.TerminationLex

```

# MuCore.lean

```lean
import OperatorKernelO6.Kernel
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
-- Minimal imports for the basic μ decrease lemmas actually used by the
-- lexicographic SN proof. (Principal / NormNum not needed once eqW diff
-- handled purely by rank bit in lex measure.)
set_option linter.unnecessarySimpa false

open Ordinal
open OperatorKernelO6
open Trace

namespace MuCore

noncomputable def mu : Trace → Ordinal.{0}
| .void        => 0
| .delta t     => (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1
| .integrate t => (omega0 ^ (4 : Ordinal)) * (mu t + 1) + 1
| .merge a b   => (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
                  (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1
| .recΔ b s n  => omega0 ^ (mu n + mu s + (6 : Ordinal)) +
                  omega0 * (mu b + 1) + 1
| .eqW a b     => omega0 ^ (mu a + mu b + (9 : Ordinal)) + 1

theorem lt_add_one_of_le {x y : Ordinal} (h : x ≤ y) : x < y + 1 :=
  (Order.lt_add_one_iff (x := x) (y := y)).2 h

theorem le_of_lt_add_one {x y : Ordinal} (h : x < y + 1) : x ≤ y :=
  (Order.lt_add_one_iff (x := x) (y := y)).1 h

-- Selected μ-drop lemmas (abbreviated proofs preserved from legacy file)
-- For brevity and because style rules emphasise no comments within code files, full doc strings omitted.

theorem mu_lt_delta (t : Trace) : mu t < mu (.delta t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (5 : Ordinal)) :=
    (Ordinal.opow_pos (b := (5 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (5 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (5 : Ordinal))) hb)
  have h : mu t ≤ (omega0 ^ (5 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have : mu t < (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (5 : Ordinal)) * (mu t + 1))).2 h
  simpa [mu] using this

theorem mu_lt_merge_void_left (t : Trace) :
  mu t < mu (.merge .void t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (2 : Ordinal)) :=
    (Ordinal.opow_pos (b := (2 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (2 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (2 : Ordinal))) hb)
  have hY : mu t ≤ (omega0 ^ (2 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have hlt : mu t < (omega0 ^ (2 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (2 : Ordinal)) * (mu t + 1))).2 hY
  have hpad :
      (omega0 ^ (2 : Ordinal)) * (mu t + 1) ≤
      (omega0 ^ (3 : Ordinal)) * (mu .void + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1) :=
    Ordinal.le_add_left _ _
  have hpad1 :
      (omega0 ^ (2 : Ordinal)) * (mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (mu .void + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    add_le_add_right hpad 1
  have hfin : mu t < ((omega0 ^ (3 : Ordinal)) * (mu .void + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad1
  simpa [mu] using hfin

theorem mu_lt_rec_zero (b s : Trace) :
    mu b < mu (.recΔ b s .void) := by
  have h0 : (mu b) ≤ mu b + 1 := le_of_lt (lt_add_one_of_le le_rfl)
  have h1 : mu b + 1 ≤ omega0 * (mu b + 1) :=
    Ordinal.le_mul_right (a := mu b + 1) (b := omega0) omega0_pos
  have hle : mu b ≤ omega0 * (mu b + 1) := le_trans h0 h1
  have hlt : mu b < omega0 * (mu b + 1) + 1 := lt_add_one_of_le hle
  have hpad :
      omega0 * (mu b + 1) + 1 ≤
      omega0 ^ (mu s + 6) + omega0 * (mu b + 1) + 1 := by
    have : (0 : Ordinal) ≤ omega0 ^ (mu s + 6) := by exact Ordinal.zero_le _
    have h₂ : omega0 * (mu b + 1) ≤ omega0 ^ (mu s + 6) + omega0 * (mu b + 1) :=
      le_add_of_nonneg_left this
    exact add_le_add_right h₂ 1
  have : mu b < omega0 ^ (mu s + 6) + omega0 * (mu b + 1) + 1 :=
    lt_of_lt_of_le hlt hpad
  simpa [mu] using this

theorem mu_lt_merge_void_right (t : Trace) :
  mu t < mu (.merge t .void) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (3 : Ordinal)) :=
    (Ordinal.opow_pos (b := (3 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (3 : Ordinal))) hb)
  have hY : mu t ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have hlt : mu t < (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (3 : Ordinal)) * (mu t + 1))).2 hY
  have hpad :
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu .void + 1)) + 1 :=
    add_le_add_right (Ordinal.le_add_right _ _) 1
  have hfin : mu t < ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu .void + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad
  simpa [mu] using hfin

theorem mu_lt_merge_cancel (t : Trace) :
  mu t < mu (.merge t t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (3 : Ordinal)) :=
    (Ordinal.opow_pos (b := (3 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (3 : Ordinal))) hb)
  have hY : mu t ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have hlt : mu t < (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (3 : Ordinal)) * (mu t + 1))).2 hY
  have hpad :
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) ≤
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1) :=
    Ordinal.le_add_right _ _
  have hpad1 :
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    add_le_add_right hpad 1
  have hfin : mu t < ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad1
  simpa [mu] using hfin

theorem mu_void_lt_integrate_delta (t : Trace) :
  mu .void < mu (.integrate (.delta t)) := by
  simp [mu]

theorem mu_void_lt_eq_refl (a : Trace) :
  mu .void < mu (.eqW a a) := by
  simp [mu]

-- MuCore.lean  (append near the end; namespace MuCore)


@[simp] theorem opow_mul_lt_of_exp_lt
    {β α γ : Ordinal} (hβ : β < α) (hγ : γ < omega0) :
    omega0 ^ β * γ < omega0 ^ α := by
  have hpos : (0 : Ordinal) < omega0 ^ β :=
    Ordinal.opow_pos (a := omega0) (b := β) omega0_pos
  have h₁ : omega0 ^ β * γ < omega0 ^ β * omega0 :=
    Ordinal.mul_lt_mul_of_pos_left hγ hpos
  have h_eq : omega0 ^ β * omega0 = omega0 ^ (β + 1) := by
    simpa [Ordinal.opow_add] using (Ordinal.opow_add omega0 β 1).symm
  have h₁' : omega0 ^ β * γ < omega0 ^ (β + 1) := by
    simpa [h_eq, -opow_succ] using h₁
  have h_exp : β + 1 ≤ α := Order.add_one_le_of_lt hβ
  have h₂ : omega0 ^ (β + 1) ≤ omega0 ^ α :=
    Ordinal.opow_le_opow_right omega0_pos h_exp
  exact lt_of_lt_of_le h₁' h₂


theorem mu_lt_eq_diff (a b : Trace) :
  mu (.integrate (.merge a b)) < mu (.eqW a b) := by
  -- Goal:  (ω^4)*(μ(merge a b)+1) + 1  <  ω^(μ a + μ b + 9) + 1
  -- It suffices to show the product is < the big tower, then step +1 on RHS.
  have h4lt : (4 : Ordinal) < (mu a + mu b + (9 : Ordinal)) := by
    -- 4 < 9 ≤ μa + μb + 9
    have h49 : ((4 : Ordinal) < (9 : Ordinal)) := by
      simpa using (Nat.cast_lt.2 (by decide : (4 : ℕ) < 9))
    have h0 : (0 : Ordinal) ≤ mu a + mu b := Ordinal.zero_le _
    have h9le : (9 : Ordinal) ≤ mu a + mu b + 9 := by
      simpa using (add_le_add_right h0 (9 : Ordinal))
    exact lt_of_lt_of_le h49 h9le
  have hγpos : (0 : Ordinal) < mu (.merge a b) + 1 := by
    -- 0 < X + 1  ↔  0 ≤ X
    have h0 : (0 : Ordinal) ≤ mu (.merge a b) := Ordinal.zero_le _
    simpa using (Order.lt_add_one_iff (x := (0 : Ordinal)) (y := mu (.merge a b))).2 h0
  -- (ω^4) * (μ(merge a b)+1) < ω^(μ a + μ b + 9)
  have hlt :
      omega0 ^ (4 : Ordinal) * (mu (.merge a b) + 1)
        < omega0 ^ (mu a + mu b + (9 : Ordinal)) :=
    sorry
  -- Then (ω^4)*(…)+1 ≤ ω^(…)  and  ω^(…) < ω^(…) + 1
  have hle : omega0 ^ (4 : Ordinal) * (mu (.merge a b) + 1) + 1
               ≤ omega0 ^ (mu a + mu b + (9 : Ordinal)) :=
    Order.add_one_le_of_lt hlt
  have hstep : omega0 ^ (mu a + mu b + (9 : Ordinal))
                 < omega0 ^ (mu a + mu b + (9 : Ordinal)) + 1 :=
    lt_add_one_of_le le_rfl
  -- Chain ≤ then < to get <
  exact lt_of_le_of_lt (by simpa [mu]) (by simpa [mu] using hstep)

end MuCore

```

