import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna
/-!
Operational Incompleteness - Lean skeleton (sorry-free)
This file is intentionally off the main import chain. It encodes:
- A structure `InternallyDefinableMeasure` capturing the intended contract.
- P1: Branch realism - per-clause rfl checks and a minimal counterexample.
- P2: Duplication realism - additive non-drop demonstration on a toy calculus.
- P2DM: Robust fix via DM multiset extension (Dershowitz–Manna) on ℕ.
- P2MPO: A compact MPO-style precedence/status weight that orients the rule.
- P3: Symbol realism - one success, and commented NameGate/TypeGate examples.

No external axioms, no `sorry`.
-/
set_option linter.unnecessarySimpa false
namespace OpIncomp

/-- A barebones measure contract. The intent is that `beta` carries the base order.
We do not commit to any concrete `beta` here. Users can instantiate with (e.g.)
lex products of `{0,1}`, DM multisets, and ordinals. -/
structure InternallyDefinableMeasure (α : Type) where
  beta     : Type
  lt       : beta -> beta -> Prop
  wf       : WellFounded lt
  m        : α -> beta
  /- Context monotonicity placeholder: in a real instantiation, this expresses
    that the measure is compatible with KO7 contexts. Kept as a Prop to avoid sorry. -/
  ctxMono  : Prop
  /- Duplication safety placeholder: per-rule, every RHS piece is < the removed redex
    in the base order. Kept as a Prop; proofs are supplied in concrete modules. -/
  piecesLt : Prop

/- P1: Branch realism. Define a two‑clause function and test a purported law. -/
namespace P1

-- A simple function with two defining clauses.
def f : Nat -> Nat
  | 0     => 0
  | _+1   => 1

-- Clause 1 (x = 0): rfl check succeeds for the instance `2 * f 0 = f (2 * 0)`.
example : 2 * f 0 = f (2 * 0) := by
  -- LHS: 2 * 0 = 0 by definitional reduction; RHS: f 0 = 0.
  rfl

-- Clause 2 (x = succ n): the global equation (forall x, 2 * f x = f (2 * x)) fails.
-- We give a minimal counterexample at x = 1.
example : 2 * f 1 ≠ f (2 * 1) := by
  -- reduces to 2 ≠ 1
  -- lhs = 2 * 1 = 2; rhs = f 2 = 1
  change (2 : Nat) ≠ 1
  decide

end P1

/- P2: Duplication realism on a tiny toy calculus. -/
namespace P2

inductive Term : Type
  | unit : Term
  | s    : Term -> Term
  | pair : Term -> Term -> Term
  deriving DecidableEq, Repr

open Term

/-- A simple additive size measure. -/
def size : Term -> Nat
  | unit      => 1
  | s t       => size t + 1
  | pair a b  => size a + size b + 1

-- A duplicating step shape: pair (s x) y -> pair x (pair y y).
-- We show explicitly the additive non-drop: size(after) = size(before) + size(y).

theorem dup_additive_failure (x y : Term) : size (pair x (pair y y)) = size (pair (s x) y) + size y := by
  simp [size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

-- Corollary: there is no strict drop under the additive `size` measure.
-- This captures the additive failure before switching to a DM/MPO measure.
theorem not_strict_drop (x y : Term) : ¬ size (pair x (pair y y)) < size (pair (s x) y) := by
  -- Suppose size (after) < size (before); rewrite via dup_additive_failure.
  intro hlt
  have hlt' : size (pair (s x) y) + size y < size (pair (s x) y) := by
    simpa [dup_additive_failure x y] using hlt
  have hle : size (pair (s x) y) ≤ size (pair (s x) y) + size y :=
    Nat.le_add_right _ _
  have : size (pair (s x) y) < size (pair (s x) y) :=
    Nat.lt_of_le_of_lt hle hlt'
  exact Nat.lt_irrefl _ this

/- Robust fix (commentary): orient the rule with a DM-multiset or MPO using an
explicit precedence/status so that both RHS pieces are strictly < the LHS redex
in the base order. Then lift to the multiset extension. If any piece cannot be
shown < redex, raise a CONSTRAINT BLOCKER. -/

end P2

/-! P2Lex: A tiny lexicographic witness that both RHS pieces are strictly
smaller than the removed LHS redex in a simple base order. This illustrates
the lex approach without external libraries. -/
namespace P2Lex
open P2

abbrev Weight := Nat × Nat

def lexLT (a b : Weight) : Prop :=
  a.fst < b.fst ∨ (a.fst = b.fst ∧ a.snd < b.snd)

def wRedex (x y : Term) : Weight := (1, P2.size (P2.Term.pair (P2.Term.s x) y))
def wPieceX (x : Term) : Weight := (0, P2.size x)
def wPieceY (y : Term) : Weight := (0, P2.size y)

theorem wPieceX_lt_redex (x y : Term) : lexLT (wPieceX x) (wRedex x y) := by
  -- 0 < 1, so the left disjunct holds.
  left; exact Nat.zero_lt_one

theorem wPieceY_lt_redex (x y : Term) : lexLT (wPieceY y) (wRedex x y) := by
  -- 0 < 1, so the left disjunct holds.
  left; exact Nat.zero_lt_one

end P2Lex

/-! P2DM: Lift the per-piece strict drops to a DM multiset drop on ℕ. -/
namespace P2DM
open P2
open Multiset

/- Base-type: ℕ with its standard <. We orient
   pair (s x) y → pair x (pair y y)
   by showing {size x, size y} <ₘ {size (pair (s x) y)}. -/

local infix:70 " <ₘ " => Multiset.IsDershowitzMannaLT

@[simp] lemma size_redex (x y : Term) :
    P2.size (P2.Term.pair (P2.Term.s x) y) = P2.size x + P2.size y + 2 := by
  have h0 : P2.size (P2.Term.pair (P2.Term.s x) y)
            = P2.size x + 1 + P2.size y + 1 := by
    simp [P2.size, Nat.add_assoc, Nat.add_comm]
  have h1 : P2.size x + 1 + P2.size y + 1 = P2.size x + P2.size y + 1 + 1 := by
    ac_rfl
  have h2 : P2.size x + P2.size y + 1 + 1 = P2.size x + P2.size y + 2 := by
    simp
  simp [h0, h1, h2]

lemma size_pieceX_lt_redex (x y : Term) :
    P2.size x < P2.size (P2.Term.pair (P2.Term.s x) y) := by
  -- size x < (size y + 2) + size x ≡ size x + (size y + 2)
  have hpos : 0 < P2.size y + 2 := by exact Nat.succ_pos (P2.size y + 1)
  have hx : P2.size x < P2.size x + (P2.size y + 2) := by
    -- from 0 < size y + 2, add size x on the left
    have := Nat.add_lt_add_left hpos (P2.size x)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- map to size of redex
  simpa [size_redex, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hx

lemma size_pieceY_lt_redex (x y : Term) :
    P2.size y < P2.size (P2.Term.pair (P2.Term.s x) y) := by
  have hpos : 0 < P2.size x + 2 := by exact Nat.succ_pos (P2.size x + 1)
  -- size y < (size x + 2) + size y = size x + size y + 2
  have hy : P2.size y < (P2.size x + 2) + P2.size y := by
    -- from 0 < size x + 2, add size y on the right
    have := Nat.add_lt_add_right hpos (P2.size y)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  simpa [size_redex, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy

/- The DM orientation: {size x, size y} <ₘ {size redex}. -/
theorem dm_orient_dup (x y : Term) :
    ({P2.size x} + {P2.size y}) <ₘ ({P2.size (P2.Term.pair (P2.Term.s x) y)}) := by
  classical
  -- Witness X = 0, Y = {size x} + {size y}, Z = {size redex}
  refine ⟨(0 : Multiset Nat), ({P2.size x} + {P2.size y}), {P2.size (P2.Term.pair (P2.Term.s x) y)}, ?hZ, by simp, by simp, ?hY⟩
  · simp  -- Z ≠ 0 (singleton nonempty)
  · intro y' hy'
    -- every y' in Y is < the sole element of Z
    rcases mem_add.mp hy' with hyx | hyy
    · have hx : y' = P2.size x := by simpa using hyx
      refine ⟨P2.size (P2.Term.pair (P2.Term.s x) y), by simp, ?_⟩
      simpa [hx] using size_pieceX_lt_redex x y
    · have hy0 : y' = P2.size y := by simpa using hyy
      refine ⟨P2.size (P2.Term.pair (P2.Term.s x) y), by simp, ?_⟩
      simpa [hy0] using size_pieceY_lt_redex x y

end P2DM

/-! P2MPO: A compact MPO-style precedence/status weight. We encode a
    precedence where head s > (others), and pair compares lex on the first
    argument’s head rank before considering sizes. This orients
    pair (s x) y > pair x (pair y y) immediately at the first position. -/
namespace P2MPO
open P2

/- Head rank: 2 for s-headed terms, 1 otherwise. -/
@[simp] def headRank : Term → Nat
  | Term.s _      => 2
  | _             => 1

/- A simple MPO-inspired weight for terms headed by `pair`.
   For non-`pair`, use a fallback. -/
@[simp] def weight : Term → Nat × Nat × Nat
  | Term.pair a b => (headRank a, P2.size a, P2.size b)
  | Term.s t      => (2, P2.size t, 0)
  | Term.unit     => (0, 0, 0)

/- Strict lexicographic order on triple Nat. -/
def ltW (u v : Nat × Nat × Nat) : Prop :=
  u.1 < v.1 ∨ (u.1 = v.1 ∧ (u.2.1 < v.2.1 ∨ (u.2.1 = v.2.1 ∧ u.2.2 < v.2.2)))

lemma ltW_of_fst_lt {a b : Nat × Nat × Nat} (h : a.1 < b.1) : ltW a b := Or.inl h

/- MPO orientation witness: RHS < LHS under ltW ∘ weight. -/
theorem mpo_orient_dup (x y : Term) :
    ltW (weight (P2.Term.pair x (P2.Term.pair y y))) (weight (P2.Term.pair (P2.Term.s x) y)) := by
  -- Case-split on x; either headRank strictly increases (unit/pair), or it ties (s t) and size increases.
  cases x with
  | unit =>
    -- headRank 1 < 2
    left; simp [weight, headRank]
  | s t =>
    -- First components tie at 2; use second component size strictly increasing.
    right
    constructor
    · simp [weight, headRank]
    · left
      -- size (s t) < size (s (s t))
      have : P2.size t + 1 < P2.size t + 2 := Nat.lt_succ_self (P2.size t + 1)
      -- align second components
      simpa [weight, headRank, P2.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | pair a b =>
    -- headRank 1 < 2
    left; simp [weight, headRank]

end P2MPO

/- P3: Symbol realism. -/
namespace P3

-- Success (NameGate/TypeGate): `size` is defined (arity 1).
#check P2.size

/- Unknown identifier example (commented to keep build green):
-- #check kappa    -- NameGate: unknown identifier `kappa` in this environment.
-/

/- Arity/type mismatch example (commented):
-- #check Nat.add 1 2 3  -- TypeGate: `Nat.add` expects 2 args, 3 supplied.
-/

end P3

end OpIncomp
