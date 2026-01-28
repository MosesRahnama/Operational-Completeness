MuCore.lean:44:73
Tactic state
1 goal
x : Ordinal.{u_1}
hx : x + 1 ≤ ω ^ (x + 1)
this : ω ^ 3 * (x + 1) ≤ ω ^ 3 * ω ^ (x + 1)
h✝ : ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω)
⊢ ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4
Expected type
x : Ordinal.{u_1}
hx : x + 1 ≤ ω ^ (x + 1)
this : ω ^ 3 * (x + 1) ≤ ω ^ 3 * ω ^ (x + 1)
⊢ ω ^ 3 * (x + 1) ≤ ω ^ 3 * ω ^ (x + 1)
Messages (4)
MuCore.lean:44:2
type mismatch, term
  this
after simplification has type
  ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) : Prop
but is expected to have type
  ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 : Prop
MuCore.lean:38:0
[diag] Diagnostics ▼
  [reduction] unfolded reducible declarations (max: 44, num: 1): ▶
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
MuCore.lean:38:0
[diag] Diagnostics ▼
  [reduction] unfolded declarations (max: 822, num: 15): ▶
  [reduction] unfolded instances (max: 1912, num: 36): ▶
  [reduction] unfolded reducible declarations (max: 304, num: 8): ▶
  [type_class] used instances (max: 80, num: 2): ▶
  [def_eq] heuristic for solving `f a =?= f b` (max: 54, num: 6): ▶
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
MuCore.lean:44:2
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 1 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 4 
[Meta.Tactic.simp.rewrite] opow_add:1000:
      ω ^ (x + 4)
    ==>
      ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] _root_.mul_le_mul_iff_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] _root_.mul_le_mul_iff_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.rewrite] ge_iff_le:1000:
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4
    ==>
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 1 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left, failed to synthesize instance
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left discharge ❌️
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] mul_le_mul_left, failed to synthesize instance
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] mul_le_mul_left discharge ❌️
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left, failed to synthesize instance
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left discharge ❌️
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] mul_le_mul_left, failed to synthesize instance
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] mul_le_mul_left discharge ❌️
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
All Messages (20)
MuCore.lean:41:43
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] Order.succ_le_iff_isMax:1000, failed to unify
      Order.succ ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
      Order.succ x ≤ ω ^ x * ω
    ==>
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_self_iff_false:1000, failed to unify
      ?x < ?x
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right':1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left':1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right:1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left:1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] Order.succ_le_iff_isMax:1000, failed to unify
      Order.succ ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
      Order.succ x ≤ ω ^ x * ω
    ==>
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_self_iff_false:1000, failed to unify
      ?x < ?x
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right':1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left':1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right:1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left:1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
MuCore.lean:44:2
type mismatch, term
  this
after simplification has type
  ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) : Prop
but is expected to have type
  ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 : Prop
MuCore.lean:38:0
[diag] Diagnostics ▼
  [reduction] unfolded reducible declarations (max: 44, num: 1): ▶
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
MuCore.lean:38:0
[diag] Diagnostics ▼
  [reduction] unfolded declarations (max: 822, num: 15): ▶
  [reduction] unfolded instances (max: 1912, num: 36): ▶
  [reduction] unfolded reducible declarations (max: 304, num: 8): ▶
  [type_class] used instances (max: 80, num: 2): ▶
  [def_eq] heuristic for solving `f a =?= f b` (max: 54, num: 6): ▶
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
MuCore.lean:44:2
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 1 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 4 
[Meta.Tactic.simp.rewrite] opow_add:1000:
      ω ^ (x + 4)
    ==>
      ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] _root_.mul_le_mul_iff_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] _root_.mul_le_mul_iff_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.rewrite] ge_iff_le:1000:
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4
    ==>
      ω ^ 3 * Order.succ x ≤ ω ^ x * ω ^ 4 
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 1 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left, failed to synthesize instance
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left discharge ❌️
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] mul_le_mul_left, failed to synthesize instance
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] mul_le_mul_left discharge ❌️
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left, failed to synthesize instance
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left discharge ❌️
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] mul_le_mul_left, failed to synthesize instance
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] mul_le_mul_left discharge ❌️
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 3 * Order.succ x ≤ ω ^ 3 * (ω ^ x * ω) 
MuCore.lean:49:43
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] Order.succ_le_iff_isMax:1000, failed to unify
      Order.succ ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
      Order.succ x ≤ ω ^ x * ω
    ==>
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_self_iff_false:1000, failed to unify
      ?x < ?x
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right':1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left':1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right:1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left:1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.unify] Order.succ_le_iff_isMax:1000, failed to unify
      Order.succ ?a ≤ ?a
    with
      Order.succ x ≤ ω ^ x * ω 
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
      Order.succ x ≤ ω ^ x * ω
    ==>
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_self_iff_false:1000, failed to unify
      ?x < ?x
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right':1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left':1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_right:1000, failed to unify
      ?a < ?a * ?b
    with
      x < ω ^ x * ω 
[Meta.Tactic.simp.unify] lt_mul_iff_one_lt_left:1000, failed to unify
      ?a < ?b * ?a
    with
      x < ω ^ x * ω 
MuCore.lean:51:2
type mismatch, term
  this
after simplification has type
  ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) : Prop
but is expected to have type
  ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 : Prop
MuCore.lean:46:0
[diag] Diagnostics ▼
  [reduction] unfolded reducible declarations (max: 44, num: 1): ▶
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
MuCore.lean:46:0
[diag] Diagnostics ▼
  [reduction] unfolded declarations (max: 822, num: 15): ▶
  [reduction] unfolded instances (max: 1912, num: 36): ▶
  [reduction] unfolded reducible declarations (max: 302, num: 8): ▶
  [type_class] used instances (max: 80, num: 2): ▶
  [def_eq] heuristic for solving `f a =?= f b` (max: 54, num: 6): ▶
use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
MuCore.lean:51:2
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 1 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 3 
[Meta.Tactic.simp.rewrite] opow_add:1000:
      ω ^ (x + 3)
    ==>
      ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] _root_.mul_le_mul_iff_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] _root_.mul_le_mul_iff_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_left:1000, failed to unify
      ?a * ?b ≤ ?a * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.rewrite] ge_iff_le:1000:
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3
    ==>
      ω ^ 2 * Order.succ x ≤ ω ^ x * ω ^ 3 
[Meta.Tactic.simp.unify] add_comm:1000:perm, failed to unify
      ?a + ?b
    with
      x + 1 
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
      x + 1
    ==>
      Order.succ x 
[Meta.Tactic.simp.rewrite] opow_succ:1000:
      ω ^ Order.succ x
    ==>
      ω ^ x * ω 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left, failed to synthesize instance
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left discharge ❌️
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] mul_le_mul_left, failed to synthesize instance
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] mul_le_mul_left discharge ❌️
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{u_1} 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right':1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left':1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] self_le_mul_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_right:1000, failed to unify
      ?a ≤ ?a * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] le_mul_iff_one_le_left:1000, failed to unify
      ?a ≤ ?b * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right':1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left':1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_right:1000, failed to unify
      ?a * ?b ≤ ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_iff_le_one_left:1000, failed to unify
      ?a * ?b ≤ ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left, failed to synthesize instance
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] _root_.mul_le_mul_iff_left discharge ❌️
      MulLeftReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_iff_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.discharge] mul_le_mul_left, failed to synthesize instance
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.discharge] mul_le_mul_left discharge ❌️
      PosMulReflectLE Ordinal.{u_1} 
[Meta.Tactic.simp.unify] mul_le_mul_right:1000, failed to unify
      ?b * ?a ≤ ?c * ?a
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_left_of_neg:1000, failed to unify
      ?c * ?a ≤ ?c * ?b
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
[Meta.Tactic.simp.unify] mul_le_mul_right_of_neg:1000, failed to unify
      ?a * ?c ≤ ?b * ?c
    with
      ω ^ 2 * Order.succ x ≤ ω ^ 2 * (ω ^ x * ω) 
MuCore.lean:56:2
Function expected at
  mu
but this term has type
  ?m.1396

Note: Expected a function because this term is being applied to the argument
  (.integrate (.merge a b))
MuCore.lean:56:33
Function expected at
  mu
but this term has type
  ?m.1396

Note: Expected a function because this term is being applied to the argument
  (.eqW a b)
MuCore.lean:58:21
Function expected at
  mu
but this term has type
  x✝

Note: Expected a function because this term is being applied to the argument
  a
MuCore.lean:59:21
Function expected at
  mu
but this term has type
  x✝

Note: Expected a function because this term is being applied to the argument
  b
MuCore.lean:71:6
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{?u.2961} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{?u.2961} 
[Meta.Tactic.simp.unify] le_add_iff_nonneg_right:1000, failed to unify
      ?a ≤ ?a + ?b
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.discharge] le_add_iff_nonneg_left, failed to synthesize instance
      AddRightReflectLE Ordinal.{?u.2961} 
[Meta.Tactic.simp.discharge] le_add_iff_nonneg_left discharge ❌️
      AddRightReflectLE Ordinal.{?u.2961} 
[Meta.Tactic.simp.unify] self_le_add_right:1000, failed to unify
      ?a ≤ ?a + ?b
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.unify] self_le_add_left:1000, failed to unify
      ?a ≤ ?b + ?a
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.rewrite] zero_add:1000:
      0 + 5
    ==>
      5 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{?u.2961} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{?u.2961} 
[Meta.Tactic.simp.unify] le_add_iff_nonneg_right:1000, failed to unify
      ?a ≤ ?a + ?b
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.discharge] le_add_iff_nonneg_left, failed to synthesize instance
      AddRightReflectLE Ordinal.{?u.2961} 
[Meta.Tactic.simp.discharge] le_add_iff_nonneg_left discharge ❌️
      AddRightReflectLE Ordinal.{?u.2961} 
[Meta.Tactic.simp.unify] self_le_add_right:1000, failed to unify
      ?a ≤ ?a + ?b
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.unify] self_le_add_left:1000, failed to unify
      ?a ≤ ?b + ?a
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.unify] le_refl:1000, failed to unify
      ?a ≤ ?a
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.discharge] le_of_subsingleton, failed to synthesize instance
      Subsingleton Ordinal.{?u.2961} 
[Meta.Tactic.simp.discharge] le_of_subsingleton discharge ❌️
      Subsingleton Ordinal.{?u.2961} 
[Meta.Tactic.simp.unify] le_add_iff_nonneg_right:1000, failed to unify
      ?a ≤ ?a + ?b
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.discharge] le_add_iff_nonneg_left, failed to synthesize instance
      AddRightReflectLE Ordinal.{?u.2961} 
[Meta.Tactic.simp.discharge] le_add_iff_nonneg_left discharge ❌️
      AddRightReflectLE Ordinal.{?u.2961} 
[Meta.Tactic.simp.unify] self_le_add_right:1000, failed to unify
      ?a ≤ ?a + ?b
    with
      5 ≤ B + 5 
[Meta.Tactic.simp.unify] self_le_add_left:1000, failed to unify
      ?a ≤ ?b + ?a
    with
      5 ≤ B + 5 
MuCore.lean:72:56
unknown tactic
MuCore.lean:72:36
type mismatch
  lt_of_lt_of_le ?m.9821
has type
  ?m.9689 ≤ ?m.9690 → ?m.9688 < ?m.9690 : Prop
but is expected to have type
  4 < B + 5 : Prop
MuCore.lean:72:52
unsolved goals
Trace : Sort u_1
x✝ : Sort u_2
mu : x✝
a b : Trace
A : Ordinal.{?u.2961} := sorry
hA : A = sorry
B : Ordinal.{?u.2961} := sorry
hB : B = sorry
C : Ordinal.{?u.2961} := A + B
hC : C = A + B
hA1 : ω ^ 3 * (A + 1) ≤ ω ^ (A + 4)
hB1 : ω ^ 2 * (B + 1) ≤ ω ^ (B + 3)
five_le : 5 ≤ B + 5
⊢ ?m.9688 < ?m.9689
MuCore.lean:67:33
unsolved goals
Trace : Sort u_1
x✝ : Sort u_2
mu : x✝
a b : Trace
A : Ordinal.{?u.2961} := sorry
hA : A = sorry
B : Ordinal.{?u.2961} := sorry
hB : B = sorry
C : Ordinal.{?u.2961} := A + B
hC : C = A + B
hA1 : ω ^ 3 * (A + 1) ≤ ω ^ (A + 4)
hB1 : ω ^ 2 * (B + 1) ≤ ω ^ (B + 3)
five_le : 5 ≤ B + 5
this : 4 < B + 5
⊢ A + 4 < C + 5
MuCore.lean:56:50
unsolved goals
Trace : Sort u_1
x✝ : Sort u_2
mu : x✝
a b : Trace
A : Ordinal.{?u.2961} := sorry
hA : A = sorry
B : Ordinal.{?u.2961} := sorry
hB : B = sorry
C : Ordinal.{?u.2961} := A + B
hC : C = A + B
hA1 : ω ^ 3 * (A + 1) ≤ ω ^ (A + 4)
hB1 : ω ^ 2 * (B + 1) ≤ ω ^ (B + 3)
hA4_lt : A + 4 < C + 5
⊢ sorry < sorry