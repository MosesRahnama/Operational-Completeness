import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination
import Init.WF                                  -- WellFounded, InvImage.wf
import Mathlib.Data.Prod.Lex                    -- Prod.Lex, WellFounded.prod_lex
import OperatorKernelO6.Meta.Patch2025_08_10
import Mathlib.SetTheory.Ordinal.Basic          -- omega0_pos, etc.
import Mathlib.SetTheory.Ordinal.Arithmetic     -- Ordinal.add_*, mul_*
import Mathlib.SetTheory.Ordinal.Exponential    -- Ordinal.opow_*, opow_le_opow_right
import Mathlib.Algebra.Order.SuccPred           -- Order.lt_add_one_iff, etc.
import Mathlib.Data.Nat.Cast.Order.Basic        -- Nat.cast_le, Nat.cast_lt

open Ordinal
open OperatorKernelO6
open Trace
open MetaSN

namespace Meta


/-- Top-level `recΔ` indicator: 1 if the term is `recΔ _ _ _`, else 0. -/
def kappaTop : Trace → Nat
| recΔ _ _ _ => 1
| _ => 0

@[simp] lemma kappaTop_rec (b s n : Trace) : kappaTop (recΔ b s n) = 1 := rfl
@[simp] lemma kappaTop_void : kappaTop void = 0 := rfl
@[simp] lemma kappaTop_delta (t : Trace) : kappaTop (delta t) = 0 := rfl
@[simp] lemma kappaTop_integrate (t : Trace) : kappaTop (integrate t) = 0 := rfl
@[simp] lemma kappaTop_merge (a b : Trace) : kappaTop (merge a b) = 0 := rfl
@[simp] lemma kappaTop_eqW (a b : Trace) : kappaTop (eqW a b) = 0 := rfl

def LexNatOrdTop : (Nat × Ordinal) → (Nat × Ordinal) → Prop :=
  Prod.Lex (· < ·) (· < ·)

lemma wf_LexNatOrdTop : WellFounded LexNatOrdTop := by
    have wfN : WellFounded (fun a b : Nat => a < b) := Nat.lt_wfRel.wf
    have wfO : WellFounded (fun a b : Ordinal => a < b) := Ordinal.lt_wf
    exact WellFounded.prod_lex wfN wfO

noncomputable def μκTop (t : Trace) : Nat × Ordinal := (kappaTop t, mu t)

-- keep diagnostics light to avoid noise during build
set_option maxHeartbeats 80000
set_option linter.unusedSimpArgs false
set_option diagnostics true

lemma μ_to_μκ_top {t t' : Trace} (h : mu t' < mu t) (hk : kappaTop t' = kappaTop t) :
    LexNatOrdTop (μκTop t') (μκTop t) := by
    unfold LexNatOrdTop μκTop
    -- identical first components: use right
    rw [hk]
    exact Prod.Lex.right _ h

/- Helper lemma for the `R_rec_zero` case -------------------------------------/
-- (obsolete) no longer needed with `kappaTop`

/- Main lemma: combined (κ, μ) measure strictly decreases for every Step -----/

theorem mu_kappa_decreases_lex :
  ∀ {a b : Trace}, Step a b → LexNatOrdTop (μκTop b) (μκTop a) := by
  intro a b h
  cases h with
  | @R_int_delta t =>
      have h_mu : mu void < mu (integrate (delta t)) := mu_void_lt_integrate_delta t
      have h_k : kappaTop void = kappaTop (integrate (delta t)) := by simp
      exact μ_to_μκ_top h_mu h_k
  | R_merge_void_left =>
    have h_mu : mu b < mu (merge void b) := mu_lt_merge_void_left b
    cases b with
    | void =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | delta t =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | integrate t =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | merge a c =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | recΔ b' s n =>
      unfold LexNatOrdTop μκTop
      apply Prod.Lex.left
      simp [kappaTop]
    | eqW a c =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
  | R_merge_void_right =>
    have h_mu : mu b < mu (merge b void) := mu_lt_merge_void_right b
    cases b with
    | void =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | delta t =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | integrate t =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | merge a c =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | recΔ b' s n =>
      unfold LexNatOrdTop μκTop
      apply Prod.Lex.left
      simp [kappaTop]
    | eqW a c =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
  | R_merge_cancel =>
    have h_mu : mu b < mu (merge b b) := mu_lt_merge_cancel b
    cases b with
    | void =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | delta t =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | integrate t =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | merge a c =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
    | recΔ b' s n =>
      unfold LexNatOrdTop μκTop
      apply Prod.Lex.left
      simp [kappaTop]
    | eqW a c =>
      simpa [kappaTop] using μ_to_μκ_top h_mu (by simp [kappaTop])
  | @R_rec_zero b s =>
      have hμ : mu b < mu (recΔ b s void) := mu_lt_rec_base b s
      cases hb : b with
      | recΔ b' s' n' =>
          -- equal kappaTop (both 1), rely on μ decrease
          have : kappaTop (recΔ b' s' n') = kappaTop (recΔ b s void) := by simp
          -- target is b (t') source is recΔ b s void (t)
          -- we need Lex μκTop b μκTop (recΔ b s void)
          -- so pass hμ and equality
          simpa [hb] using (μ_to_μκ_top (t' := b) (t := recΔ b s void) hμ (by simp [hb]))
      | void
      | delta _
      | integrate _
      | merge _ _
      | eqW _ _ =>
          -- kappaTop drops 1 -> 0, left decrease
          unfold LexNatOrdTop μκTop
          apply Prod.Lex.left
          simp [kappaTop, hb]
  | @R_eq_refl a =>
      have h_mu : mu void < mu (eqW a a) := mu_void_lt_eq_refl a
      have h_k : kappaTop void = kappaTop (eqW a a) := by simp
      exact μ_to_μκ_top h_mu h_k
  | @R_eq_diff a b _ =>
      have h_mu : mu (integrate (merge a b)) < mu (eqW a b) := mu_lt_eq_diff a b
      have h_k : kappaTop (integrate (merge a b)) = kappaTop (eqW a b) := by simp
      exact μ_to_μκ_top h_mu h_k
  | R_rec_succ b s n =>
      -- left strictly drops: 0 < 1
      unfold LexNatOrdTop μκTop
      apply Prod.Lex.left
      simp [kappaTop]

/- Strong normalization via the lexicographic measure -------------------------/

theorem strong_normalization_lex : WellFounded (fun a b => Step b a) := by
    have wf_lex : WellFounded LexNatOrdTop := wf_LexNatOrdTop
    refine Subrelation.wf ?_ (InvImage.wf (f := μκTop) wf_lex)
    intro x y hxy; simpa using mu_kappa_decreases_lex hxy





end Meta
