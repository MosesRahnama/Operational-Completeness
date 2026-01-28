# Post-Mortem — Strong Normalisation Proof Attempts

**OperatorKernelO6**  ·  Last update: 2025-08-14

This file records _every_ strategy that has been tried so far, why it
**looked plausible**, where the hidden flaw lay, and how long it took
Lean to expose the mistake.  Each section ends with _Early-Warning
Signals_ we should watch for in future designs.

> "If you eliminate the impossible, whatever remains—no matter how
> improbable—must be the truth.  This document is our catalogue of the
> impossible." — Project maxim

---
## 0  The Problem in One Line

```
recΔ b s (δ n)   →   merge s (recΔ b s n)
```
A proof measure must _decrease strictly_ across this rule **even though**
`merge` duplicates `s` and `δ` can be nested arbitrarily deep.

---
## 1  Ordinal-Only (μ) — "rec_succ_bound"

| Ingredient | Idea |
|------------|------|
| μ : Ordinal | Defined by transfinite recursion on `Trace`. |

* **Assumption**  Every rule, including `rec_succ`, lowers μ.
* **Hidden step** Introduced an un-proved lemma
  `rec_succ_bound : μ(merge …) < μ(recΔ … (δ _))`.
* **Lean verdict** Green _only_ with `sorry`.

### Fatal flaw
Ordinal recursion could not separate `δ` from its parent term.  The
lemma was **false**; the proof would require transfinite arithmetic that
violated earlier `μ` equations.

### Early-warning signals
* Any measure that does not examine **shape** (δ vs. non-δ) is doomed.
* Presence of a single hard-wired `sorry` at the very heart of the
  induction tree.

---
## 2  κ = `Nat.max` Depth (+1 bump)

| Ingredient      | Value                                    |
|-----------------|-------------------------------------------|
| κ(recΔ … δ n)   | `base + 1`                               |
| κ(recΔ … n)     | `base`                                   |
| base            | `max (max κb κs) κn`                     |

* **Assumption** `+1` guarantees κ-drop.
* **Lean counter-example** Take `n = δ m`; then κ on both sides is
  `base + 1` ⇒ _no drop_.

### Fatal flaw
Constant slack is neutralised by _one level_ of nesting.  This is a
shape-blind bump.

### Early-warning signals
* Equality of κ on LHS/RHS whenever the predecessor term already matches
  the bump pattern.

---
## 3  Constant Escalation (+2, +3, …)

Same as §2 but with bigger constants.

### Fatal flaw
Any finite constant can be cancelled by **one extra nested δ**.  The
problem is structural, not quantitative.

### Early-warning signals
* "If +k fails, maybe +k+1" — infinite ladder of constants.

---
## 4  κ + μ Lexicographic (Termination_Lex v0)

* **Assumption** Let κ detect six easy rules, fall back to μ for
  `rec_succ`.
* **Implement** Revived `rec_succ_bound` under μ branch.

### Fatal flaw
We smuggled the original **false** inequality back in.  Nothing new was
proven.

### Early-warning signals
* Any attempt to _“hand the hot potato”_ back to μ without a new true
  inequality.

---
## 5  κ (+2) with Helper Lemmas (KappaPlus2.lean)

* **Attempt** Prove `kappa_drop_recSucc` by bounding κ(rec) ≤ base+1.
* **Lean** Goal reduced to `⊢ False` in the `n = δ _` branch.

### Fatal flaw
The internal bound `κ(rec … n) ≤ base+1` is **wrong** precisely when
`n` is δ-shaped.

### Early-warning signals
* A proof that starts with `cases n` but assumes a universal equation.

---
## 6  Boolean δ-Flag + (κ, μ)

| Measure         | Value         |
|-----------------|---------------|
| flag            | 1 if top-form is `recΔ … (δ _)`, else 0 |

* **Assumption** Lexicographic triple will drop flag on `rec_succ`.
* **Counter-example** `merge void t` **increases** flag from 0 to 1 if
  `t` is bad.

### Fatal flaw
Flag can _increase_ on unrelated rules → outer lexicographic component
is not monotone.

### Early-warning signals
* Any Boolean (0/1) measure affected by argument duplication.

---
## 7  ρ Counter – Counting Bad Nodes

| Measure ρ(t) | `# { recΔ _ _ (δ _) sub-nodes of t }` |

* **Assumption** ρ drops by 1 on `rec_succ`.
* **Counter-example** `merge s …` duplicates `s`; if `s` carries _k_
  bad nodes, RHS adds _k_ — net change ≥ 0.

### Fatal flaw
Duplication creates unbounded positive swings.  No additive counter can
outpace it.

### Early-warning signals
* Presence of rules that **duplicate** sub-terms containing the bad
  pattern.

---
## 8  Claude_SN Branch (87 % Green)

Kept a single explicit `sorry` for the problematic inequality.  Valuable
as a sanity check but still axiom-dependent.

---
## 9  Lessons & Red Flags Checklist

1. **Shape blindness** – Any scalar bump (Nat or Ordinal) that ignores
   nested δ’s will fail.
2. **Duplication** – If your measure is additive, inspect every rule for
   term duplication.  Merge rules are the usual culprits.
3. **False rescue** – Re-introducing a previously false lemma under a
   different name does not make it true.
4. **Single-bit flags** – 0/1 indicators seldom survive duplication;
   prefer graded or structural data.
5. **Infinite constant ladder** – If success depends on “pick k large
   enough,” stop and analyse structure instead of magnitude.
6. **Hidden `sorry` at core** – Treat as _red alert_; you are borrowing
   correctness.

---
## 10  Viable Unexplored Directions

| Direction | Why it dodges known pitfalls |
|-----------|-----------------------------|
| **Multiset / MPO** | Duplication never increases a multiset w.r.t. its extension order.  Shape captured via precedence. |
| **Sized-type Index** | Encodes the δ-depth of the third argument; strictly decreases on `rec_succ`, unaffected by merge duplication. |
| **Semantic labelling** | Tag terms with ordinal annotations derived from their position; known to tame recursors. |

---
### Closing Motto
> _“You can’t fight math, but you can fight the **wrong** math early.”_

May this file serve as our radar for spotting doomed assumptions before
we code.
