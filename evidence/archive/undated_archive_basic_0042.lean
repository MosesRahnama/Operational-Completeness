namespace OperatorMath

/-
  An operator language built without external numerals or booleans.
  The constructors are the only primitives we allow ourselves.
-/
inductive OpTerm : Type
| seed : OpTerm
| wrap : OpTerm -> OpTerm
| weave : OpTerm -> OpTerm -> OpTerm
deriving Repr, DecidableEq

open OpTerm

/-
  `Subterm` captures the immediate-subterm relation.  Every proof of
  termination will be routed through this purely structural ordering.
-/
inductive Subterm : OpTerm -> OpTerm -> Prop
| wrap {t} : Subterm t (wrap t)
| left {t u} : Subterm t (weave t u)
| right {t u} : Subterm u (weave t u)

/-
  Every operator term is accessible with respect to `Subterm`.  The proof
  is structural: from a node we only recurse to its immediate components.
-/
def subtermAcc : forall t : OpTerm, Acc Subterm t
| seed =>
    Acc.intro seed (by
      intro y h
      cases h)
| wrap t =>
    let ht := subtermAcc t
    Acc.intro (wrap t) (by
      intro y h
      cases h with
      | wrap => exact ht)
| weave t u =>
    let ht := subtermAcc t
    let hu := subtermAcc u
    Acc.intro (weave t u) (by
      intro y h
      cases h with
      | left => exact ht
      | right => exact hu)

def subterm_wf : WellFounded Subterm :=
  WellFounded.intro subtermAcc

/-
  Primitive reduction rules: each step strictly exposes a structural
  component of the operator it started from.
-/
inductive Step : OpTerm -> OpTerm -> Prop
| unwrap {t} : Step t (wrap t)
| takeLeft {t u} : Step t (weave t u)
| takeRight {t u} : Step u (weave t u)

@[simp] theorem step_to_subterm {a b : OpTerm} (h : Step a b) : Subterm a b :=
  by
    cases h with
    | unwrap => exact Subterm.wrap
    | takeLeft => exact Subterm.left
    | takeRight => exact Subterm.right

def subtermAcc_to_stepAcc : forall {t : OpTerm}, Acc Subterm t -> Acc Step t
| t, Acc.intro _ h =>
    Acc.intro t (fun y hy =>
      subtermAcc_to_stepAcc (h y (step_to_subterm hy)))

def step_wf : WellFounded Step :=
  WellFounded.intro (fun t =>
    subtermAcc_to_stepAcc (subtermAcc t))

def Normal (t : OpTerm) : Prop :=
  forall {u}, Step u t -> False

@[simp] theorem seed_normal : Normal seed :=
  by
    intro u h
    cases h

end OperatorMath
