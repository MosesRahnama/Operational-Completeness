
I want to see if I can build a full mathematical system purely using operators. That is, no numbers, no axioms, no lean helpers, nothing. Define everything from scratch ground. And get to the proofs of all of it. Termination confluence, Godel.

C:\Users\Moses\central-servers\basic.lean

Sorry here.

Starting from pure operators is a fascinating program, but in Lean you can’t literally erase the foundational machinery: Lean’s calculi (dependent type theory, universes, β/η reduction, etc.) are always present, so any “axiom‑free” development is still riding on those intrinsic rules. What you can do is stay inside your own namespace, avoid importing mathlib, and treat Lean’s core as a metalanguage in which you encode an operator algebra that you supply with all of its own primitives, rewrite rules, and meta-properties.

I’d suggest tackling it in stages:

Operator language. Fix a small inductive syntax (e.g. Trace) along the lines you’ve started, adding constructors that correspond to the primitive operations you want allowed. Build structural recursion/induction principles explicitly so you aren’t sneaking in convenience lemmas.
Evaluation / rewriting. Define a judgment (as an inductive family) that captures how one operator expression rewrites to another. Keep it entirely synthetic—no numeric counters, just structural operators.
Meta-theory. Prove normalization/termination with well-founded recursion on whatever ordering you define. Then layer confluence proofs (likely by Newmann’s lemma equivalents) inside your operator universe.
Arithmetic & higher structures. Encode numerals, tuples, etc., as particular operator terms; define addition/multiplication as operators over those encodings; prove the Peano-style laws internally. From there you can bootstrap rings, fields, etc., again purely as operator identities.
Gödel-ish endpoints. When you reach self-referential statements, you’ll have to implement syntax/semantics for “proofs” inside your operator calculus and show how the encoding sidesteps the incompleteness barriers—or, more realistically, reproduce the usual Gödel machinery in this operator language and show how it manifests.
Lean will enforce termination of definitions, so for strong normalization arguments you might need to mirror them as theorems rather than rely solely on Lean’s kernel. To keep everything “from scratch,” avoid importing modules and stick to the elaborator, using only the primitive constants in the prelude (or disable even those by working in a new theory file with set_option pp.notation false etc.).

If you’d like, we can start by expanding basic.lean with the syntactic layer (evaluation relation, congruence lemmas), then iteratively climb toward arithmetic and the meta-theorems. Let me know which layer you want to tackle first.

Well, my question is even my question is, is it even possible? To prove termination for an operator only system. It can be anything else. These are just, you know. What I came up with.

Termination Feasibility

Proving termination for a purely-operator system is absolutely doable; what you need is a well-founded measure on expressions so every rewrite strictly decreases it. That measure can live entirely inside your operator syntax (e.g., “size of the syntax tree,” “height,” “multiset of suboperators”) with no appeal to external numerals—just structural recursion.
Classical term‑rewriting provides many templates: combinatory logic without typing fails to terminate (since SK can loop), while simply-typed λ-calculus, typed SK systems, and numerous orthogonal rewrite systems are strongly normalizing because their rewrite rules are oriented by well-founded orders like multiset or recursive path orders.
In Lean you’d encode your operators and the rewrite relation inductively, then prove that relation is well-founded—either by explicitly building a well-founded order on traces or by importing general theorems (if you allow that). Lean checks that your proof certifies the absence of infinite chains; it doesn’t require Peano numerals or external axioms, just the meta-level notion of well-foundedness.
Confluence proofs (Newman’s Lemma, critical-pair analysis) can likewise be internalized using only operator syntax; once you have strong normalization and local confluence, global confluence follows entirely within the operator universe.
Handling Gödel-style arguments is tougher: to reproduce incompleteness you need enough arithmetic to encode statements and proofs inside your operator language, so at some point you effectively rebuild arithmetic as operator terms. That’s conceptually consistent with the “operators only” goal, but it forces you to define a rich enough meta-layer to talk about self-reference.

If you want to experiment, a good next step is to specify a tiny operator calculus, define a rewrite relation, and try to craft a structural measure that decreases under every rewrite so Lean can certify it's well-founded. Let me know if you want help setting up that skeleton.

But did they? Get you know, did they prove using just operators? There was no external encoding, nothing. Just what you define here. That's it. No chair chains, no boolean encoding. etc.

If by “just operators” you mean a calculus whose syntax consists only of your primitive operator constructors and whose proofs never appeal to any background numerals, booleans, lists, etc., then yes—termination proofs can still go through. What is essential is a well-founded ordering on your operator terms; that ordering can itself be defined using only the same operators.

A standard structural route is:

Define an inductive relation ≺ over your operator trees (for example: a term is greater than each of its immediate subterms, and closed under multiset extension). This relation lives wholly inside the operator syntax; it never mentions numbers or external encodings.
Prove, by induction on constructors, that ≺ is well-founded. In Lean this is routine once the relation is inductively generated; the kernel checks that there are no infinite descending ≺ chains.
Show that every rewrite step in your system strictly decreases ≺. With those two ingredients, Lean delivers strong normalization: there can be no infinite rewrite sequence.
This style is how termination is established for many higher-order rewrite systems and typed λ-calculi. Textbook proofs often describe the measure using natural numbers or ordinals for explanatory convenience, but you can internalize the same reasoning: represent the measure as operator terms (e.g., “height” becomes a unary operator nested as deep as the term is tall) and prove the decrease lemma structurally.

So the answer is that nothing forces you to import external arithmetic or boolean gadgets. You do need to craft the structural ordering carefully, because—as you hinted—systems like untyped SK combinatory logic don’t terminate: there exist rewrite loops regardless of proof technique. But when the rewrite rules really are terminating, building a well-founded relation purely from your operators is both possible and already well-trodden territory in rewriting theory (Knuth–Bendix, Tait/Girard reducibility, higher-order path orders, etc.), just specialized to your bespoke syntax.

Do you think you can design it? Honestly, it's just my idea. And I want to see if it's possible. To be honest, I haven't done much research on it either, and I'm not a mathematician, so you're gonna have to lead.

Operator Skeleton

Added a minimal operator calculus OpTerm with primitives seed, wrap, and weave, giving you a universe built purely from operators (basic.lean:7).
Defined the immediate-subterm ordering Subterm and proved its well-foundedness via the structural accessibility lemma subtermAcc, avoiding any numerical measures (basic.lean:19, basic.lean:28, basic.lean:48).
Introduced core rewrite steps (wrap-unfold and projections on weave) and established that every step strictly decreases along Subterm, yielding the well-founded reduction relation step_wf (basic.lean:55, basic.lean:67).
Captured the notion of normal forms inside the operator universe with Normal, illustrating how termination statements are phrased without external encodings (basic.lean:76).
Next steps you might take:

Add a reflexive–transitive closure of Step and prove unique normal forms (confluence) by structural arguments.
Layer a compositional semantics on top of OpTerm (still using operators) so you can represent “truth” and “proof traces” internally.
Begin encoding arithmetic objects (e.g., numerals as iterated wrap/weave) and verify Peano-like identities entirely within this operator language.
Explore self-reference by building an operator-level syntax for proofs, paving the way toward Gödel-style fixed points.
Let me know when you’re ready to extend the system in one of those directions.

View all changes
basic.lean

Yeah, but now we're defining logic. Why subterm? OK. Hold on. Yeah, but why? Why would it be? I mean, we're ordering like actually we're introducing structural ordering. We need to define structural ordering.

Subterm is the structural ordering. It lives entirely inside the operator universe: every constructor just says “this immediate component sits below the node that contains it,” so it never appeals to numbers, booleans, or external encodings (basic.lean:19). The accessibility proof (basic.lean:28) is a structural recursion on the shape of the operator term, and WellFounded.intro subtermAcc (basic.lean:48) merely packages that structural fact; we could even restate the same idea in a custom inductive predicate if you’d rather avoid Lean’s Acc/WellFounded names. The key point is that to certify termination we must order rewrite steps by something that always decreases, and the “strictly smaller subterm” relation is the canonical way to make that ordering explicit without importing numeric measures. If you want to see a bespoke version (e.g., your own StructOrder and Terminates definitions), we can layer that next so the entire argument stays couched in your operator language symbols.

There seem to be errors here. Do you think we should define a lean project? But add it to gitignore?

a : OpTerm
⊢ Acc Step a
type mismatch
Acc Step x
has type
Prop : Type
but is expected to have type
Acc ?m.3580 x → Sort ?u.3562 : Type ?u.3562

No goals
a x : OpTerm
ih : ∀ (y : OpTerm), Subterm y x → Acc Subterm y
y : OpTerm
hy : Subterm y x
⊢ Step x y
Application type mismatch: In the application
step_to_subterm hy
the argument
hy
has type
Subterm y x : Prop
but is expected to have type
Step x y : Prop


Reworked the structural ordering so everything type-checks inside a single Lean file—no extra project needed. Key updates: the primitive operator syntax is unchanged, but Step now points from a reduct to its source so it lines up with the structural relation (basic.lean:55). Using that orientation, step_to_subterm embeds rewrite steps into the subterm order (basic.lean:60), subtermAcc_to_stepAcc lifts the accessibility proof from subterms to steps (basic.lean:67), and step_wf packages the resulting well-foundedness (basic.lean:72). Normal forms now mean “no reduct below this node,” matching the new relation (basic.lean:76), and seed_normal discharges by contradiction (basic.lean:79). I ran lean basic.lean to confirm the file is clean.

Natural next moves:

Define the reflexive/transitive closure of Step and show uniqueness of normal forms via structural arguments.
Layer additional operators that encode data (like iterated wrap) and demonstrate how arithmetic laws would live entirely inside this operator universe.
1 file changed

Undo

View all changes
basic.lean

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



