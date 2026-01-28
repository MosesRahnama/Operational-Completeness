# MuPort.lean

- Source: `MuPort.lean`
- Generated: 2025-08-14T00:26:04

```lean
/- DOOMED APPROACH — DO NOT USE (project policy) -/
/- • Do NOT attempt μ-drop on R_rec_succ via any global “rec_succ_bound”.
     It is false in general. This harness proves κ strictly drops on rec_succ
     and uses μ only for the other seven rules (incl. eqW_diff).
   • Do NOT revive positivity-only opow_mul_lt_of_exp_lt. Use principal additivity
     and ω-power normality instead (opow_add, strictMono, principal_add_omega0_opow).
   • For eqW_diff, follow: merge-payload bound → ω^4 lift → principal-add; no tower-swap hacks. -/

-------YOU CAN SUGGEST SOLUTIONS TO SALVAGE THIS APPROACH. BUT NEED PERMISSION TO DO SO.

import OperatorKernelO6.Kernel
import Init.WF
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic

open Ordinal
open OperatorKernelO6
open Trace

namespace OperatorKernelO6.Meta

-- Reuse mu from MuCore (assumed imported elsewhere). If not, user must ensure ordering of imports.

/-- Strict monotonicity wrapper for ω-powers in the exponent. -/
@[simp] lemma opow_lt_opow_right' {b c : Ordinal} (h : b < c) :
    omega0 ^ b < omega0 ^ c := by
  simpa using ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

/-- Finite absorption on the left when target is ≥ ω. -/
lemma nat_left_add_absorb' {n : ℕ} {p : Ordinal} (h : omega0 ≤ p) :
    (n : Ordinal) + p = p := by
  -- Mathlib lemma name alignment (try both modern and legacy naming)
  simpa using (Ordinal.natCast_add_of_omega0_le (n := n) h)

lemma one_left_add_absorb' {p : Ordinal} (h : omega0 ≤ p) :
    (1 : Ordinal) + p = p := by
  simpa using (Ordinal.one_add_of_omega0_le h)

/-- Triple-sum bounded by an additive principal ω^κ using principality. -/
lemma omega_pow_add3_lt'
    {κ α β γ : Ordinal}
    (hκ : 0 < κ) (hα : α < omega0 ^ κ) (hβ : β < omega0 ^ κ) (hγ : γ < omega0 ^ κ) :
    α + β + γ < omega0 ^ κ := by
  have hprin := Ordinal.principal_add_omega0_opow κ
  have hsum : α + β < omega0 ^ κ := hprin hα hβ
  have hsum' : α + β + γ < omega0 ^ κ := hprin hsum hγ
  simpa [add_assoc] using hsum'

/-- Helper: bound merge head contribution under ω^(μ a + μ b + 5). -/
lemma termA_le' (x : Ordinal) :
  (omega0 ^ (3 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) := by
  have hx : x + 1 ≤ omega0 ^ (x + 1) := by
    simpa using Ordinal.right_le_opow (a := omega0) (b := x + 1) one_lt_omega0
  have hmul : (omega0 ^ (3 : Ordinal)) * (x + 1) ≤
      (omega0 ^ (3 : Ordinal)) * (omega0 ^ (x + 1)) :=
    mul_le_mul_left' hx (omega0 ^ (3 : Ordinal))
  have hrewrite : (omega0 ^ (3 : Ordinal)) * (omega0 ^ (x + 1)) =
      omega0 ^ ((3 : Ordinal) + (x + 1)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Ordinal.opow_add (a := omega0) (b := (3 : Ordinal)) (c := x + 1)).symm
  simpa [hrewrite, add_assoc, add_comm, add_left_comm] using hmul

/-- Helper: bound merge tail contribution under ω^(μ a + μ b + 5). -/
lemma termB_le' (x : Ordinal) :
  (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 3) := by
  have hx : x + 1 ≤ omega0 ^ (x + 1) := by
    simpa using Ordinal.right_le_opow (a := omega0) (b := x + 1) one_lt_omega0
  have hmul : (omega0 ^ (2 : Ordinal)) * (x + 1) ≤
      (omega0 ^ (2 : Ordinal)) * (omega0 ^ (x + 1)) :=
    mul_le_mul_left' hx (omega0 ^ (2 : Ordinal))
  have hrewrite : (omega0 ^ (2 : Ordinal)) * (omega0 ^ (x + 1)) =
      omega0 ^ ((2 : Ordinal) + (x + 1)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Ordinal.opow_add (a := omega0) (b := (2 : Ordinal)) (c := x + 1)).symm
  simpa [hrewrite, add_assoc, add_comm, add_left_comm] using hmul

/-- Core bound: `μ (merge a b) + 1 < ω^(μ a + μ b + 5)`. -/
lemma merge_inner_bound_simple'
  (mu : Trace → Ordinal)
  (a b : Trace)
  (hmu : True) :  -- placeholder to keep signature distinct if base file already declares mu
  let C : Ordinal := mu a + mu b;
  (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
    (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 2 < omega0 ^ (C + 5) := by
  intro C
  have h_head := termA_le' (x := mu a)
  have h_tail := termB_le' (x := mu b)
  have h_exp1 : mu a + 4 < C + 5 := by
    have : mu a ≤ C := Ordinal.le_add_right _ _
    have : mu a + 4 ≤ C + 4 := add_le_add_right this 4
    have : C + 4 < C + 5 := add_lt_add_left (by decide : (4:Ordinal) < 5) C
    exact lt_of_le_of_lt ‹_› this
  have h_exp2 : mu b + 3 < C + 5 := by
    have : mu b ≤ C := Ordinal.le_add_left _ _
    have : mu b + 3 ≤ C + 3 := add_le_add_right this 3
    have : C + 3 < C + 5 := add_lt_add_left (by decide : (3:Ordinal) < 5) C
    exact lt_of_le_of_lt ‹_› this
  have h1_pow : (omega0 ^ (3 : Ordinal)) * (mu a + 1) < omega0 ^ (C + 5) :=
    lt_of_le_of_lt h_head (opow_lt_opow_right' h_exp1)
  have h2_pow : (omega0 ^ (2 : Ordinal)) * (mu b + 1) < omega0 ^ (C + 5) :=
    lt_of_le_of_lt h_tail (opow_lt_opow_right' h_exp2)
  have h_fin : (2 : Ordinal) < omega0 ^ (C + 5) := by
    have two_lt_omega : (2 : Ordinal) < omega0 := nat_lt_omega0 2
    have omega_le : omega0 ≤ omega0 ^ (C + 5) := by
      have one_le_exp : (1 : Ordinal) ≤ C + 5 := by
        have : (1 : Ordinal) ≤ (5 : Ordinal) := by norm_num
        exact le_trans this (le_add_left _ _)
      calc
        omega0 = omega0 ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
        _ ≤ omega0 ^ (C + 5) := Ordinal.opow_le_opow_right omega0_pos one_le_exp
    exact lt_of_lt_of_le two_lt_omega omega_le
  have k_pos : (0 : Ordinal) < C + 5 := by
    have : (0 : Ordinal) < (5 : Ordinal) := by norm_num
    exact lt_of_lt_of_le this (le_add_left _ _)
  have : (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
         (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 2 < omega0 ^ (C + 5) :=
    omega_pow_add3_lt' k_pos h1_pow h2_pow h_fin
  simpa [C] using this

/-- Special case for both void arguments. -/
lemma mu_lt_eq_diff_both_void'
  (mu : Trace → Ordinal) :
  (omega0 ^ (4 : Ordinal)) * ((omega0 ^ (3 : Ordinal)) + (omega0 ^ (2 : Ordinal)) + 2) + 1 <
    omega0 ^ (9 : Ordinal) + 1 := by
  have h3 : omega0 ^ (3 : Ordinal) < omega0 ^ (5 : Ordinal) :=
    opow_lt_opow_right' (by decide : (3:Ordinal) < 5)
  have h2 : omega0 ^ (2 : Ordinal) < omega0 ^ (5 : Ordinal) :=
    opow_lt_opow_right' (by decide : (2:Ordinal) < 5)
  have h_fin : (2 : Ordinal) < omega0 ^ (5 : Ordinal) := by
    have two_lt_omega : (2 : Ordinal) < omega0 := nat_lt_omega0 2
    have omega_le : omega0 ≤ omega0 ^ (5 : Ordinal) := by
      have one_le_exp : (1 : Ordinal) ≤ (5 : Ordinal) := by norm_num
      calc
        omega0 = omega0 ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
        _ ≤ omega0 ^ (5 : Ordinal) := Ordinal.opow_le_opow_right omega0_pos one_le_exp
    exact lt_of_lt_of_le two_lt_omega omega_le
  have tri := omega_pow_add3_lt' (by norm_num : (0:Ordinal) < 5) h3 h2 h_fin
  have h_mul : omega0 ^ (4 : Ordinal) * (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) <
               omega0 ^ (4 : Ordinal) * omega0 ^ (5 : Ordinal) :=
    Ordinal.mul_lt_mul_of_pos_left tri (Ordinal.opow_pos (b := (4:Ordinal)) omega0_pos)
  have h_exp : omega0 ^ (4 : Ordinal) * omega0 ^ (5 : Ordinal) = omega0 ^ (9 : Ordinal) := by
    have : (4:Ordinal) + (5:Ordinal) = 9 := by norm_num
    simpa [this] using
      (Ordinal.opow_add (a := omega0) (b := (4:Ordinal)) (c := (5:Ordinal))).symm
  have h_core := lt_of_lt_of_eq h_mul h_exp
  have : omega0 ^ (4 : Ordinal) * (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) + 1 <
       omega0 ^ (9 : Ordinal) + 1 :=
    lt_add_one_of_le (Order.add_one_le_of_lt h_core)
  simpa using this

end OperatorKernelO6.Meta

-------YOU CAN SUGGEST SOLUTIONS TO SALVAGE THIS APPROACH. BUT NEED PERMISSION TO DO SO.

```
