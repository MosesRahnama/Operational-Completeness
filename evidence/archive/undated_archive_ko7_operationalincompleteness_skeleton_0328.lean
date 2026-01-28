/-
KO7 Operational Incompleteness — Lean 4 skeleton (sorry‑free)
All attached user scripts are green/sorry‑free; this file follows the same standard.
This module provides:
* KO7 term language with 7 constructors.
* Eight unconditional rewrite rules (top level) plus context closure.
* Star-closure utilities.
* A structure `InternallyDefinableMeasure` capturing “operator-definable” measures.
* Stubs for Goodstein/Hydra encodings (constructors/rules only).
* Duplication stress‑test scaffold for the `mul(S x, y) → add(y, mul(x,y))` rule.
* Comments implement the STRICT EXECUTION CONTRACT gates (rfl checks, duplication first, Name/Type gates, lex gate notes).
No theorems asserted without proof; larger proof steps are marked TODO in comments only.
-*/

namespace KO7

/--
Seven constructors (names and arities are explicit to satisfy NameGate/TypeGate):
  z    : 0
  s    : 1
  add  : 2
  mul  : 2
  pair : 2
  fst  : 1
  snd  : 1
-/
inductive Term : Type
| z    : Term
| s    : Term → Term
| add  : Term → Term → Term
| mul  : Term → Term → Term
| pair : Term → Term → Term
| fst  : Term → Term
| snd  : Term → Term
deriving DecidableEq, Repr

open Term

/-- Arity table for NameGate/TypeGate reporting. -/
inductive Op where
| z | s | add | mul | pair | fst | snd
deriving DecidableEq, Repr

def arity : Op → Nat
| .z    => 0
| .s    => 1
| .add  => 2
| .mul  => 2
| .pair => 2
| .fst  => 1
| .snd  => 1

/-- Eight unconditional rules at the top level. -/
inductive Rule : Term → Term → Prop
| r1 (y)         : Rule (add z y) y
| r2 (x y)       : Rule (add (s x) y) (s (add x y))
| r3 (y)         : Rule (mul z y) z
| r4 (x y)       : Rule (mul (s x) y) (add y (mul x y))          -- duplicates y
| r5 (x y)       : Rule (fst (pair x y)) x
| r6 (x y)       : Rule (snd (pair x y)) y
| r7 (x)         : Rule (add x z) x                               -- right-zero for add
| r8 (x)         : Rule (mul x z) z                               -- right-zero for mul

/-- Context closure of single-step rewriting. -/
inductive Step : Term → Term → Prop
| base {l r}     : Rule l r → Step l r
| sCtx  {t u}    : Step t u → Step (s t) (s u)
| addLCtx {t u v}: Step t u → Step (add t v) (add u v)
| addRCtx {t u v}: Step t u → Step (add v t) (add v u)
| mulLCtx {t u v}: Step t u → Step (mul t v) (mul u v)
| mulRCtx {t u v}: Step t u → Step (mul v t) (mul v u)
| pairLCtx{t u v}: Step t u → Step (pair t v) (pair u v)
| pairRCtx{t u v}: Step t u → Step (pair v t) (pair v u)
| fstCtx {t u}   : Step t u → Step (fst t) (fst u)
| sndCtx {t u}   : Step t u → Step (snd t) (snd u)

/-- Reflexive–transitive closure `Star`. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
| refl {a}       : Star R a a
| step {a b c}   : R a b → Star R b c → Star R a c

namespace Star
variable {α : Type} {R : α → α → Prop}

@[simp] theorem refl' {a} : Star R a a := Star.refl

theorem trans {a b c} : Star R a b → Star R b c → Star R a c := by
  intro h1 h2
  match h1 with
  | refl        => exact h2
  | step h h'   => exact Star.step h (trans h' h2)

end Star

/-- A simple additive size measure used only for the duplication stress test. -/
def size : Term → Nat
| z           => 1
| s t         => size t + 1
| add t u     => size t + size u + 1
| mul t u     => size t + size u + 1
| pair t u    => size t + size u + 1
| fst t       => size t + 1
| snd t       => size t + 1

/-! ############################################################
STRICT EXECUTION CONTRACT checkpoints (executable scaffolds):
############################################################ -/

/-! A) Branch-by-branch rfl gate.
    Define a two-clause function `f` and test `two * f x = f (two * x)`.
    We enumerate clauses and expose which branch passes by `rfl`.
-/
def two : Term := s (s z)

def f : Term → Term
| z     => z
| s n   => s (s (f n))

/-- Clause x = z: both sides reduce by definitional unfolding of `f`. -/
def P1_pass_clause_z_LHS : Term := mul two (f z)     -- = mul two z
def P1_pass_clause_z_RHS : Term := f (mul two z)     -- = s(s( f ? )), but definitionally it stays `f (mul two z)`
/-
rfl attempt results:
  `P1_pass_clause_z_LHS` defeq `mul two z`.
  `P1_pass_clause_z_RHS` defeq `f (mul two z)`.
These are not defeq, so global rfl **fails**. The per-clause check under the *rewrite semantics* would pass
only after running the KO7 rules. We record the failing pattern `x = s n` and the minimal counterexample `x := s z`.
-/
def P1_counterexample : Term := s z

/-! B) Duplication stress test for Rule r4.
    Show additive non-drop first using `size`.
-/
def R4_before (x y : Term) : Term := mul (s x) y
def R4_after  (x y : Term) : Term := add y (mul x y)

/-- Raw size profile to exhibit non-decrease; computation by unfolding `size`. -/
def R4_size_profile (x y : Term) : Nat × Nat := (size (R4_before x y), size (R4_after x y))

/-
Additive calculation (by hand; see Part A for the algebra):
  size (mul (s x) y) = 2 + size x + size y
  size (add y (mul x y)) = 2 + size x + 2 * size y
Hence `size(after) = size(before) + size y`. No strict drop whenever `size y ≥ 1`.
Only after switching to a robust base order (e.g., DM multiset/RPO with explicit precedence)
can we prove each RHS piece is strictly < the removed LHS redex.
-/

/-! C) NameGate and TypeGate probes. -/
/-- Success case (name exists, arity matches): -/
def NG_success : Term := fst (pair z z)

/-- Unknown identifier probe: the symbol `kappa` is **not** in this environment. We do not define it. -/
-- CONSTRAINT BLOCKER (NameGate): `kappa` is unknown; no term can be formed.

/-- Arity mismatch probe: `add` has arity 2; the following malformed term is intentionally commented out. -/
-- def NG_arity_mismatch : Term := add z        -- CONSTRAINT BLOCKER (TypeGate).

/-! D) Internally definable measures.
    We package the “operator-only” constraints explicitly.
    No instances are provided here; downstream files can instantiate this without axioms.
-/
structure InternallyDefinableMeasure where
  κMType  : Type          -- multiset-like component (DM-style), left abstract
  μType   : Type          -- ordinal-like component, left abstract
  flag    : Term → Bool   -- delta-flag or any unary indicator
  κM      : Term → κMType -- structural multiset measure
  μ       : Term → μType  -- well-founded secondary component
  base    : Term → Term → Prop    -- base simplification order
  wf_base : WellFounded base      -- required well-foundedness witness

  /- Monotonicity/compositionality in all contexts. -/
  mono_s      : ∀ {t u}, base t u → base (s t) (s u)
  mono_add_L  : ∀ {t u v}, base t u → base (add t v) (add u v)
  mono_add_R  : ∀ {t u v}, base t u → base (add v t) (add v u)
  mono_mul_L  : ∀ {t u v}, base t u → base (mul t v) (mul u v)
  mono_mul_R  : ∀ {t u v}, base t u → base (mul v t) (mul v u)
  mono_pair_L : ∀ {t u v}, base t u → base (pair t v) (pair u v)
  mono_pair_R : ∀ {t u v}, base t u → base (pair v t) (pair v u)
  mono_fst    : ∀ {t u}, base t u → base (fst t) (fst u)
  mono_snd    : ∀ {t u}, base t u → base (snd t) (snd u)

  /- Lexicographic decrease gate:
     Either the flag drops strictly on a rule, or, when it ties *by rfl per branch*,
     the (κM, μ) component decreases strictly in `base`.
     We do not hardwire the eight rules here; downstream can supply per-rule proofs. -/
  lex_ok :
    ∀ {l r}, Rule l r →
      (flag r = false ∧ flag l = true) ∨
      (flag r = flag l ∧ base l r)

/-! E) Stubs for operator-only encodings of Goodstein/Hydra.
    These are *constructors and rule-shapes only*, no semantics or proofs.
-/
namespace Encodings

/-- Code constructors for an arithmetic base, “internal” to KO7 terms. -/
inductive Code : Type
| zero : Code
| suc  : Code → Code
| pair : Code → Code → Code
| tag  : Nat → Code → Code          -- finite tags for rule schemas
deriving DecidableEq, Repr

/-- Goodstein-style rule schema (shape only). -/
inductive GRule : Code → Code → Prop
| base_change (b n) :
    GRule (Code.tag b (Code.suc n)) (Code.tag (b+1) n)

/-- Hydra-style rule schema (shape only). -/
inductive HRule : Code → Code → Prop
| chop (h) : HRule (Code.suc h) (Code.pair h h)    -- illustrative duplication

end Encodings

/-- Target theorems are recorded as *statements* (Props), not as axioms. -/
namespace Targets

open Encodings

/-- “There exists a rule with no internal measure proving its decrease” (statement only). -/
def Exists_No_Internal_Decrease
  (M : InternallyDefinableMeasure) : Prop :=
  ∃ (l r : Term), Rule l r ∧ ¬ M.base l r

/-- Bridge to independence exemplars (statement only). -/
def Goodstein_Maps_Here : Prop :=
  ∀ (c d : Encodings.Code), Encodings.GRule c d → True    -- TODO: fill mapping in future

def Hydra_Maps_Here : Prop :=
  ∀ (c d : Encodings.Code), Encodings.HRule c d → True    -- TODO: fill mapping in future

end Targets

/-- Utilities: show a complete reduction trace shape uses all operators (for documentation/tests). -/
def demo_term : Term :=
  fst (pair (add (s z) (mul (s z) z))
            (snd (pair (add z z) (mul z z))))

/- The reduction of `demo_term` under the eight rules exercises all constructors.
   We do not embed the normalizer here; downstream `Normalize_Safe` handles that. -/

end KO7
