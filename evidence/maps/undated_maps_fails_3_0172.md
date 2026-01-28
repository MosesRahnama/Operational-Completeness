Comprehensive Post‑Mortem: Strong Normalization Attempts (OperatorKernelO6)
==========================================================================

Purpose
— Map every approach we tried, why it failed, the mathematical principle behind the failure, and concrete early‑warning checks to avoid similar dead‑ends. This is an up‑front “do not enter” atlas for future work.


1) Kernel facts and the one problematic rule
-------------------------------------------

- Kernel is fixed (immutable). Seven rules are benign for well‑foundedness. One rule is hard:

  recΔ b s (δ n)  ⟶  merge s (recΔ b s n)

  It duplicates s and moves the recΔ head to the right. Any termination measure must strictly drop across this step.

- Structural signature of trouble:
  - Head symbol changes from recΔ to merge (good for precedence‑based orders).
  - The third argument loses a δ (superficially “one step closer”), but s is duplicated (bad for simple additive counters).
  - Any measure blind to duplication or nested δ’s will tie or increase.


2) μ‑only era (ordinal measure) — the “rec_succ_bound” mirage
--------------------------------------------------------------

- Idea: Define a single ordinal μ: Trace → Ordinal that strictly drops on all rules.

- Sticking point: Needed

  μ (recΔ b s (δ n)) > μ (merge s (recΔ b s n))

  Generally false. We introduced an unproven domination inequality (rec_succ_bound) that was used implicitly/explicitly to “go green”. Removing it collapsed the proof.

- Root cause: Ordinal arithmetic is non‑intuitive in three recurrent ways:
  - Right‑monotonicity fails in general: a < b does not imply a + c < b + c on the right.
  - Absorption (n + p = p) needs ω ≤ p; using it without proof is unsound.
  - “Principal add” lemmas require all summands < the target ω‑power and correct argument order.

- Lean symptom: Once the sorry/axiom is removed, calc chains around ω^k·X < ω^E and principal‑add folding fail.

- Lesson: A lone μ cannot encode both “one less δ on the right branch” and “s duplicated on the left” safely. Any rec_succ domination must be structural, not a global ordinal inequality.


3) κ with a +1 bump — “shape‑blind slack”
-----------------------------------------

- Definition:
  - Let base := max (κ b) (max (κ s) (κ n)).
  - κ (recΔ b s (δ n)) = base + 1; κ (recΔ b s n) = base when n is not δ.

- Intended: rec_succ should drop κ.

- Failure (nested δ land mine): If n = δ m, then κ (recΔ b s n) = base + 1 as well, and

  κ (merge s (recΔ b s n)) = max (κ s) (κ (recΔ b s n)) = base + 1.

  So κ ties; no strict decrease.

- Lean symptom: Any equality κ (recΔ b s n) = base fails when n is δ. Attempts to force equality with simp produce ⊢ False goals.

- Lesson: A constant bump is defeated by nested δ; κ needs shape sensitivity beyond “+k”.


4) κ with +2, +3, … — “constant escalation fallacy”
----------------------------------------------------

- Motivation: Create more slack (base + 2, +3, …) to survive one nested δ.

- Failure: The same counterexample scales. With n = δ m, both sides’ max rises by the same finite constant; duplication preserves equality.

- Lesson: No uniform additive constant will guarantee a strict drop in the presence of duplication and nested δ.


5) κ + μ lexicographic — “handing the problem back to μ”
---------------------------------------------------------

- Attempt: Use κ as primary; when κ ties, let μ strictly drop.

- Failure: To make rec_succ drop in μ, we re‑introduced the same false rec_succ_bound inequality. This is circular.

- Lesson: You can’t delegate the problematic rule to μ without reviving the unsound inequality.


6) κ(+2) with helper lemmas — “wrong bound in delta case”
----------------------------------------------------------

- Attempt: Prove a direct κ‑drop lemma for rec_succ using max/≤ facts.

- Root cause: The key step κ (recΔ b s n) ≤ base + 1 is false when n is δ_; it should be base + 2 under those definitions.

- Lean symptom: Proofs reduce to ⊢ False when trying to close with rfl/simp over kappa.

- Lesson: Any κ bound that ignores the δ/non‑δ split of n is brittle. At minimum you must cases n; but the constant‑bump model still ties (see §3/§4).


7) δ‑flag + (κ, μ) triple — “non‑monotone discriminator”
--------------------------------------------------------

- Attempt: deltaFlag(t) = 1 when the top‑level is recΔ _ _ (δ _); else 0. Use (flag, κ, μ) lex.

- Fatal counterexample:
  a = merge void (recΔ _ _ (δ _))   (flag a = 0)
  b = recΔ _ _ (δ _)                (flag b = 1)

  On the merge‑void rule, the flag increases — lex monotonicity is broken.

- Lesson: Any added discriminator must be non‑increasing on all rules except the target rule; boolean flags rarely satisfy this with duplication/reshaping.


8) ρ counter (count “bad rec_succ sites”) — “duplication sinkhole”
------------------------------------------------------------------

- Idea: ρ(t) = number of recΔ _ _ (δ _) nodes in t. Then ρ drops by 1 on rec_succ and is non‑increasing elsewhere.

- Failure: rec_succ duplicates s. Net change is ρ(after) = ρ(before) − 1 + ρ(s). If ρ(s) ≥ 1, ρ doesn’t strictly drop. With arbitrary s, you cannot bound this.

- Lesson: Simple additive counters are not robust to duplication.


9) Subtler ordinal pitfalls repeatedly hit by AIs
-----------------------------------------------

- Right‑add myth: Assuming a < b ⇒ a + c < b + c (for ordinals) — false in general on the right.
- Absorption without proof: Rewriting (n : Ord) + p = p without first proving ω ≤ p — invalid.
- “Principal add” misfires: Mis‑ordered arguments or missing hypotheses that all summands are < ω^κ.
- Exponent monotonicity confusion: Mixing ≤ and < under opow, or swapping the sides of opow_add.
- Definitional equality trap: Forcing κ (recΔ b s n) to a single base via rfl/simp; false when n is δ_.
- Phantom lemmas: Invoking Nat.max_lt_iff (not in scope), or assuming easy duals that don’t exist.
- Equate instead of bound: Demanding equality when only inequalities might hold — and those still fail in δ cases.


10) Lean diagnostics that were early red flags
---------------------------------------------

- “Missing cases”/“unexpected ‘|’” around recΔ/eqW — pattern match/structural split issues.
- “Not a definitional equality” on κ(recΔ … (δ _)) = … — ignoring κ’s δ‑split.
- Goals like κ(recΔ … n) ≤ κ b ∨ … — need le_max_iff chains, not mythical max_lt lemmas.
- Ordinal calc stuck at + finite tails — absorption/monotonicity hypotheses missing.


11) Why “quick inequality replacement” still fails for κ
--------------------------------------------------------

- Replacing equality with hrec_le: κ(recΔ … n) ≤ base and hrec: κ(recΔ … n) < base + 1 looks nice, but both are false when n = δ m under the +1 bump model, because κ(recΔ … n) = base + 1 in that branch. Lean flags ⊢ False exactly there. Same nested‑δ land mine (see §3/§4).


12) What will work (viable green paths)
----------------------------------------

- MPO/RPO (multiset‑/polynomial‑path ordering):
  - Choose a precedence with recΔ > merge ≥ others.
  - Use the multiset extension on immediate subterms. Replacing one head recΔ by the multiset {s, recΔ b s n} is strictly smaller: root precedence drops and each argument is smaller under the subterm/precedence order. Duplication of s is safe under the multiset order.
  - This is the standard duplication‑robust structural approach.

- Sized types / semantic labelling:
  - Index recΔ’s third argument with a size that strictly decreases under δ removal and is preserved elsewhere. Show non‑increase on all other rules; strict decrease on rec_succ.
  - Avoids ordinal arithmetic in the core termination step.


13) SSOT guardrails that helped (and should stay)
-------------------------------------------------

- μ has a single definition only in Meta.Termination; μ‑lemmas live in MuCore and import via open MetaSN. Prevents dual μ constants and simp/rw confusion.
- Ordinal toolkit discipline: Use qualified lemmas (opow_le_opow_right, mul_lt_mul_of_pos_left, principal_add_omega0_opow). Avoid removed upstream names and unsafe bridges.


14) Early‑warning checklist (run this before touching code)
----------------------------------------------------------

- About κ/
  - Are you proving κ(recΔ … n) = base? Stop; it’s false for n = δ _.
  - Are you relying on a constant offset (… + k) to force strictness? Produce the nested‑δ counterexample; it ties.

- About μ/
  - Is any step equivalent to “rec_succ_bound”? Stop; it’s generally false.
  - Are you using right‑monotonicity of + on ordinals without checking hypotheses? Add the missing lemma or change approach.

- About counters/flags/
  - Does your measure provably not increase under merge duplication? If not, assume it fails.
  - Does any boolean/finite flag stay non‑increasing for all non‑target rules? Check merge‑void explicitly.

- About Lean lemmas/
  - Are you invoking a non‑existent ‘max_lt_iff’ or relying on rfl for κ(recΔ … (δ _))? Expect failure.


15) One‑liners to remember (AI failure modes)
---------------------------------------------

- “Bump will save us.” It won’t; duplication neutralizes uniform offsets.
- “We’ll finish with μ.” Not without the false rec_succ_bound.
- “Equality by simp.” Not across a definition that branches on δ.
- “Count the bad nodes.” Duplication breaks additive counts.
- “Ordinals are like naturals.” No: right‑add, absorption, and principal add need proofs.


16) Next steps (recommended)
----------------------------

- Prototype MPO skeleton: define precedence and multiset measure; prove rec_succ decreases by root precedence + multiset extension; wire other rules.
- Keep SSOT for μ and continue using it for non‑structural rules (equality payloads) only when needed.
- Maintain fails_3.md as the living “red‑flag” registry; update when a new pitfall is found.


Appendix A — Minimal MPO sketch (informal)
------------------------------------------

- Define ≺ as the closure of: proper subterm; or root precedence drop.
- Define M(t) = multiset of immediate subterms of t (or a compositional encoding reflecting constructor status).
- Use multiset extension: t → t′ is decreasing if M(t′) <_ms M(t) with respect to ≺.
- For rec_succ: recΔ b s (δ n) → merge s (recΔ b s n). Precedence recΔ > merge gives a head drop; each RHS arg is a subterm or smaller by precedence. Thus M(after) <_ms M(before) despite duplication of s.

This path eliminates all constant‑offset and duplication pitfalls by design.
