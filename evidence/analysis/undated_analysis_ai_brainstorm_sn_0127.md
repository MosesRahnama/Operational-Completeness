# Plan Overview # 1

Below is a synthesis of everything in `all_suggestions.md`, contrasted with the path I have been recommending, followed by one “best-of-both-worlds” action plan.

────────────────────────────────────────
1 What everyone agrees on (solid ground)
•  The lexicographic measure μ̂(t) := (κ(t), μ(t)) under  
  `Prod.Lex (·<·) (·<·)` + `InvImage.wf` is the right scaffold.

•  κ must bump ­exactly once: +1 only at `recΔ _ _ (delta _)`.  
  With that choice the κ-drop lemma `kappaD_drop_recSucc` lets us treat every `R_rec_succ` **purely by κ**, so the notorious `rec_succ_bound` is no longer needed.

•  For the other seven rules μ-drop lemmas are already available (void→integrate, merge-void L/R, merge-cancel, rec-zero, eq-refl, eq-diff).  
  The only lemma that sometimes “goes missing” in builds is `mu_lt_eq_diff`; it lives in `Meta.Termination` and must stay visible in `MuCore`.

•  The file pair `Termination_Lex.lean + MuCore.lean` already implements this strategy end-to-end and compiles when `mu_lt_eq_diff` is in scope.

────────────────────────────────────────
2 Why other branches fail
•  `SN_Final` and the two “Claude” files keep κ equal in the `rec_succ` δ-case; that forces a μ-drop that depends on the impossible domination inequality.  
  Without a measure redesign those files will never go green.

•  `Measure.lean` and `Termination_Legacy.lean` mix the old (false) bound with newer code, generating duplicate names and “unknown identifier” noise.

────────────────────────────────────────
3 What the new opinions add
They contribute a precise recipe for finishing the **only** missing ingredient in the green path:

  • Rewrite the helper bounds `termA_le` / `termB_le` in `MuCore.lean` using  
    `opow_add`, `le_omega_pow`, and the finite-offset bridges  
    `add3_plus1_le_plus4`, `add2_plus1_le_plus3`.

  • Re-enable (or simply export) `mu_lt_eq_diff` so `Termination_Lex.lean`’s `R_eq_diff` branch compiles.

Everything else in the long document reiterates build hygiene we were already following: quarantine legacy files, don’t global-simp the non-δ rec case, normalise `Nat.max` shapes locally, keep trace noise off, etc.

────────────────────────────────────────
4 Final concrete plan (no code yet)

Step 0 (sanity check, <1 min)  
  • `lake build OperatorKernelO6.Meta.Termination_Lex` — confirm the only red comes from a missing or broken `mu_lt_eq_diff`.  
  • `grep -R \"sorry\\|admit\" Meta/*` — should list only MuCore errors you pasted.

Step 1 Fix MuCore (high-confidence mechanical edits)  
  A. At top: `import OperatorKernelO6.Meta.Termination` and `open MetaSN`.  
  B. Rewrite `termA_le`, `termB_le` exactly as outlined (use `le_omega_pow`, `opow_add`, offset lemmas; no use of right-additivity).  
  C. Delete the accidental local binder that shadows `mu`.  
  D. Remove extraneous lemma names from `simp` brackets; move them into separate `have` equalities if actually needed.  
  E. Make sure lines

```
theorem mu_lt_eq_diff (a b : Trace) :
  mu (.integrate (.merge a b)) < mu (.eqW a b)
```

   compile, then `export` it (or rely on the copy that is already in `Meta.Termination`—but do **not** create two definitions with that name).

Step 2 Harness integrity  
  A. Open `Termination_Lex.lean` and ensure its `R_eq_diff` clause imports/opens the module where `mu_lt_eq_diff` now definitely lives and calls it via `drop_right`.  
  B. Check that its κ definition is the local `kappaD`, not the one from `Kappa.lean`.  
  C. Leave `kappaD_rec_base` **not** `[simp]` (only the δ variant is).

Step 3 Quarantine legacy noise  
  A. Move `Measure.lean`, `Termination_Legacy.lean` (and any variants you know are dead ends) to a non-compiled `Archive/` folder or guard them with `if false then` style `#eval`.  
  B. Search the active code (`rg "Termination_Legacy"` etc.) to ensure no live import pulls them back in.  
  C. Confirm `lakefile.lean`/`lake-manifest.json` doesn’t enumerate those files as build targets.

Step 4 Re-export the finished theorem  
  Option A (minimal): add a tiny file

```
-- Meta/SN_Export.lean
import OperatorKernelO6.Meta.Termination_Lex
export OperatorKernelO6.MetaSNFinal (strong_normalization_final)
```

  Option B: copy the exact lex harness into `SN_Final.lean` if you want a uniform filename; just keep the code identical.

Step 5 Clean rebuild & lint  
  • `find . -name "*.olean" -delete`  
  • `lake build` — should be green.  
  • `grep -R "sorry\\|admit" Meta/*.lean` — should return nothing among active files.  
  • `#print axioms strong_normalization_final` in a scratch Lean file; it should list only the usual Lean axioms.

Step 6 Documentation pass  
  • Update `README` or a new `SN_Proof.md` to state: the official SN theorem is `strong_normalization_final` re-exported by `SN_Export.lean`; κ drops only on rec-succ, μ handles the rest; no false inequalities assumed.  
  • Add a note that legacy files are archived for historical record.

────────────────────────────────────────
5 Why this is the best merged plan

• It keeps 100 % of the verified mathematics from `Termination_Lex.lean`—the only branch known to be fully sound.  
• It resolves **all** current MuCore type mismatches by aligning them with the ordinal toolkit’s canonical lemmas (no ad-hoc tactics, no unsafe assumptions).  
• It avoids re-inventing κ or μ, so no risk of divergent measures across files.  
• It meets every acceptance criterion in the suggestions file and yours: no `rec_succ_bound`, κ-only drop on rec-succ, μ-drop everywhere else, no `[simp]` land-mines, no legacy imports, no new axioms.  
• The work is small, mechanical, and local: fix two helper lemmas, expose one µ-drop lemma, quarantine legacy files, re-export one theorem.

Once you confirm this direction, the next step would be to apply the MuCore edits and the thin export file—after which the project should build cleanly end-to-end.

────────────────────────────────────────  

# Plan Overview # 2

Checklist

Hygiene: ensure only the clean harness participates in the build.
MuCore fixes: imports, shape of termA_le/termB_le, remove brittle tactics, wire mu properly.
Harness wiring: eq_diff via μ-drop; rec_succ via κ-drop.
Optional SN_Final salvage: transplant κ-only rec_succ.
Verification: targeted builds, sorry/axioms checks, simple smoke.
Guardrails: clear “doomed approach” bans and CI checks.
Step-by-step approach

Build hygiene and single source of truth
Quarantine legacy: keep Termination_Legacy.lean and Measure.lean out of the active import graph (they’re causing duplicate decls and bad matches).
Point the official path to Termination_Lex.lean + MuCore.lean. Don’t import Termination_Legacy anywhere in the final harness.
Keep only one exported SN theorem (either re-export the one in Termination_Lex or introduce a thin SN_Export that re-exports it).
MuCore hardening (high-confidence repairs)
Bring mu into scope correctly:
Import the module that defines mu (OperatorKernelO6.Meta.Termination) and open/qualify MetaSN so mu : Trace → Ordinal.{0} is a function, not a metavariable.
Fix termA_le / termB_le target shapes:
Prove (ω^3)·(x+1) ≤ ω^(x+4) and (ω^2)·(x+1) ≤ ω^(x+3) by:
Lift x+1 ≤ ω^(x+1), then mul_le_mul_left'.
Collapse products with Ordinal.opow_add to ω^(3+(x+1)) and ω^(2+(x+1)).
Finish via Ordinal.opow_le_opow_right and the arithmetic bridges 3+(x+1) ≤ x+4 and 2+(x+1) ≤ x+3.
Replace brittle arithmetic steps:
Avoid norm_num; use Nat.cast_lt/Nat.cast_le + simple Nat facts, and add_lt_add_left to transport across A/B. Normalize with [add_assoc, add_comm, add_left_comm].
Keep the eq_diff pipeline as documented:
“merge payload” bound under a single ω^(C+5), multiply by ω^4 for integrate, fold exponents with opow_add to ω^(C+9), then “+1” bridge via Order.add_one_le_of_lt / Order.lt_add_one_iff and finish by rewriting μ.
Harness wiring (Termination_Lex)
R_eq_diff: use MuCore.mu_lt_eq_diff; κ equality via simp with Nat.max_assoc/comm/left_comm; then drop_right.
R_rec_succ: keep κ-only drop (kappaD_drop_recSucc); do not use any μ inequality there.
All other rules: unchanged—μ-drop with existing lemmas.
Optional: SN_Final salvage (if you still want it)
Replace the rec_succ delta branch with the κ-drop lemma (like Termination_Lex), removing any rec_succ_bound reference entirely.
In nested rec cases, make inner κ shapes explicit with a local equality via simp [kappa, Nat.max_*] before applying drop_left.
This yields parity with Termination_Lex without re-proving μ arithmetic.
Verification and quality gates
Targeted builds first:
Build MuCore; then build Termination_Lex.
Grep for sorry/admit in active files; they should be absent.
Axioms check (optional): #print axioms on the exported SN theorem—expect only core axioms; no new ones.
Minimal smoke: check strong_normalization_final applies to an arbitrary t (Acc StepRev t).
Guardrails to avoid regressions
Keep the “DOOMED APPROACH — DO NOT USE” banner (already inserted) in MuCore and Termination_Lex to block:
Any attempt to prove a global rec_succ_bound μ-domination.
Any revival of positivity-only opow_mul_lt_of_exp_lt.
Any “tower-swap/absorption” hacks for eq_diff.
Add a CI grep that fails the build if “rec_succ_bound” or “opow_mul_lt_of_exp_lt” (positivity-only form) appears in active files.
What’s different/better than before

Enforces “single harness” discipline and removes legacy collisions as the first step, preventing wasted cycles.
Fixes MuCore locally with ordinal-specific APIs and correct target shapes (ω^(x+4)/ω^(x+3)), eliminating the shape mismatch that caused the cascade of errors.
Locks in the correct eq_diff pipeline with principal additivity and normality only; no risky lemmas.
Offers a clean, optional path to salvage SN_Final by transplanting the κ-only rec_succ strategy (no μ bound, no logical risk).
Acceptance in one glance

κ strictly decreases only on recΔ-succ: yes.
μ decreases on the other seven rules, eq_diff via MuCore.mu_lt_eq_diff: yes.
No legacy imports in final harness: yes.
No sorry/admit in active files: required.
No banned lemmas/assumptions: required.

────────────────────────────────────────

# Plan Overview # 3


Of course. Based on a thorough review of all the provided context, here is my full evaluation and recommended path forward to achieve the final Strong Normalization proof.

### **1. Overall Assessment & Core Insight**

The project is at a critical inflection point. Numerous attempts have correctly identified that a simple ordinal measure (`μ`) is insufficient on its own, and that a lexicographic measure `(κ, μ)` is the correct path. The "dead ends" have all stemmed from the same subtle but fatal flaw: **defining a `κ` that is not robust enough to handle all 8 reduction rules consistently.**

The single most important insight gathered from the existing files and suggestions is this:

> The `R_rec_succ` rule is the lynchpin. Any successful `κ` measure must handle the `κ`-drop for the general `rec_succ` case while also remaining stable (i.e., not increasing) for all other rules. A simple binary `κ`-bit fails this test. A structural `κ` succeeds, but requires a case-split within the `R_rec_succ` proof itself.

**This case-split on `n` within the `R_rec_succ` proof is the final missing piece of the puzzle.**

### **2. The Optimal Path Forward: A Three-Component Architecture**

The best path forward is a clean, modular implementation of the **Structural `κ` + `μ` Lexicographic Proof**. This approach is mathematically robust, leverages the "Green Channel" of proven lemmas from `Termination.lean`, and avoids all the pitfalls of previous attempts.

I recommend structuring the final proof across three focused, single-responsibility files:

**Component A: The Ordinal Foundation (Existing)**
*   **File:** `OperatorKernelO6/Meta/Termination.lean`
*   **Purpose:** This file is the single source of truth for the ordinal measure `μ` and all its required decrease lemmas (`mu_lt_eq_diff`, `mu_lt_rec_base`, etc.). It has been successfully proven and is on the "Green Channel."
*   **Action:** **No changes.** This file will be imported and its `MetaSN` namespace will be used directly. We will not reinvent any ordinal arithmetic.

**Component B: The `kappa` Counter (New File)**
*   **File:** `OperatorKernelO6/Meta/Kappa.lean` (or a similar descriptive name)
*   **Purpose:** To define the **structural `κ`** and its associated `simp` lemmas. This isolates the definition into a reusable, independent module.
*   **Action:** Create this new, small file with exactly the following content:
    *   The recursive definition of `kappa : Trace → Nat`, which increments by `+1` only on `recΔ _ _ (delta _)` and uses `Nat.max` for `merge` and `eqW`.
    *   The `@[simp]` lemmas for `kappa_void`, `kappa_delta`, `kappa_integrate`, `kappa_merge`, `kappa_eqW`, and `kappa_rec_delta`.

**Component C: The Lexicographic Proof Harness (The Final Goal)**
*   **File:** `OperatorKernelO6/Meta/Claude_SN.lean`
*   **Purpose:** To wire everything together. This file will be lean and focused only on the lexicographic argument, importing the mathematical machinery from the other two components.
*   **Action:** Refactor this file to contain:
    1.  **Imports:** `Kernel`, `Termination`, and the new `Kappa` file.
    2.  **Definitions:** The lexicographic `measure (κ, μ)`, `LexOrder`, and the proof of its well-foundedness (`wf_LexOrder`).
    3.  **Helpers:** The `drop_left` and `drop_right` tactics.
    4.  **The Main Theorem:** A single, clean `measure_decreases` theorem with an exhaustive `match` over all 8 `Step` constructors.

### **3. The Definitive Proof Strategy for `measure_decreases`**

This is the core of the execution plan. Each of the 8 rules will be handled as follows within `Claude_SN.lean`:

*   **R_int_delta, R_eq_refl:**
    *   **Logic:** `κ` either drops or is equal.
    *   **Implementation:** `by_cases h : kappa t = 0`.
        *   If `h` is true, `κ` is equal. Use `drop_right` with the corresponding `μ`-lemma from `MetaSN`.
        *   If `h` is false, `κ` strictly drops. Use `drop_left`.

*   **R_merge_void_left, R_merge_void_right, R_merge_cancel, R_eq_diff:**
    *   **Logic:** `κ` is provably equal in all these cases via `Nat.max` properties.
    *   **Implementation:** Use `drop_right` with the corresponding `μ`-lemma from `MetaSN`. The `κ` equality `hk` is proven with a simple `simp` call. For `R_eq_diff`, the pattern `(a:=a) (b:=b) hneq` must be used.

*   **R_rec_zero:**
    *   **Logic:** `κ` is non-increasing (`κ(b) ≤ κ(recΔ b s void)`).
    *   **Implementation:** `by_cases hb_eq : kappa b = kappa (recΔ b s void)`.
        *   If `hb_eq` is true, `κ` is equal. Use `drop_right` with `mu_lt_rec_base`.
        *   If `hb_eq` is false, `κ` strictly drops. Use `drop_left`.

*   **R_rec_succ (The Final Hurdle):**
    *   **Logic:** The behavior of `κ` depends on the structure of `n`. A case-split is mandatory.
    *   **Implementation:** `cases n with | delta m => ... | _ => ...`
        *   **`delta m` branch:** In this specific sub-case, `κ` is **equal** on both sides of the reduction. We *must* rely on the `μ` decrease. The proof will use `drop_right`, calling the `mu_lt_rec_succ` lemma from `MetaSN` (with its required domination bound argument). The `κ` equality is proven with `simp [kappa]`.
        *   **Non-`delta` (`_`) branch:** In all other cases, `κ` **strictly decreases** (from `base + 1` to `base`). The proof is a simple `drop_left`.

### **4. Why This Path is Superior**

*   **Robustness:** The structural `κ` with the `rec_succ` case-split is the only model that correctly handles all 8 rules without contradiction.
*   **Modularity:** Separating `μ`, `κ`, and the final `SN` proof into three distinct files is clean engineering that adheres to the project's rules. It makes the code easier to understand, maintain, and verify.
*   **Leverages Proven Work:** This plan makes maximum use of the "Green Channel" by relying entirely on the already-proven lemmas in `Termination.lean`, as the project rules dictate.
*   **Finality:** This is not another experiment. This is the canonical solution that synthesizes all prior learning from the project's history. Executed precisely, it will result in a complete and correct strong normalization proof.

────────────────────────────────────────

# Plan Overview # 4


# My Comprehensive Analysis After Reading All AI Suggestions
After thoroughly analyzing all the AI suggestions, I've identified remarkable consensus on the core issues and solution. Here's my synthesized approach that combines the best insights from each:

# Core Consensus Points (All AIs Agree)
The rec_succ_bound is mathematically impossible - This inequality μ(merge s (recΔ b s n)) < μ(recΔ b s (delta n)) cannot hold globally. GPT-5 correctly identifies the exponent mismatch as insurmountable.

The lexicographic (κ, μ) approach is correct - All AIs converge on this being the right framework.

κ must drop ONLY on rec_succ - This is the lynchpin insight. By making κ strictly decrease for ALL rec_succ cases, we bypass the need for any μ inequality in that rule.

Legacy files are toxic - Termination_Legacy.lean and Measure.lean cause duplicate declarations and must be quarantined.

Critical Discovery from the Analysis
The Meta_Directory_Analysis makes a crucial claim: Termination_Lex.lean already contains a complete, clean strong-normalization proof!

If true, this changes everything - we might not need to fix anything, just use what's already there.

My Enhanced Step-by-Step Plan
Phase 1: Verify Reality (2 minutes)

# The single most important check
lake build OperatorKernelO6.Meta.Termination_Lex
grep -n "sorry" OperatorKernelO6/Meta/Termination_Lex.lean


**If this returns no sorries → Jump directly to Phase 5 (cleanup and export)**

#### **Phase 2: The Mathematical Architecture**

The correct `κ` definition (structural, not binary):
```lean
def kappaD : Trace → Nat
| .recΔ b s (.delta n) => Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n) + 1
| .recΔ b s n          => Nat.max (Nat.max (kappaD b) (kappaD s)) (kappaD n)
| all_other_cases       => [standard structural recursion]
```

**Key Insight:** κ increments by 1 ONLY when the third argument to `recΔ` is specifically `delta n`.

#### **Phase 3: The Seven μ-Drop Rules**

For these rules, we need the following lemmas (all should exist in `Termination.lean`):
- `mu_void_lt_integrate_delta` 
- `mu_lt_merge_void_left/right`
- `mu_lt_merge_cancel`
- `mu_lt_rec_base`
- `mu_void_lt_eq_refl`
- `mu_lt_eq_diff` ← This is the potentially missing piece

#### **Phase 4: The `mu_lt_eq_diff` Resolution**

GPT-5's mathematical proof is correct. The key steps:

1. **Use the finite/infinite bridges:**
   - `3 + (A+1) ≤ A+4` (for all ordinals A)
   - `2 + (B+1) ≤ B+3` (for all ordinals B)

2. **Apply principal additivity at ω^(C+5)**

3. **Use ω^a · ω^b = ω^(a+b)** for exponent folding

**But first check:** This lemma likely already exists in `Termination.lean`!

#### **Phase 5: The Optimal Implementation Path**

Based on confidence levels:

**Path A (85% likely): Termination_Lex is already complete**
1. Confirm no sorries in `Termination_Lex.lean`
2. Create `Meta/SN_Official.lean`:
   ```lean
   import OperatorKernelO6.Meta.Termination_Lex
   export MetaSNFinal (strong_normalization_final)
   ```
3. Quarantine legacy files
4. Done!

**Path B (15% likely): Minor fixes needed**
1. Check if `mu_lt_eq_diff` exists in `Termination.lean`
2. If missing, add it to `MuCore.lean` using GPT-5's proof
3. Ensure `Termination_Lex.lean` imports the correct module
4. Fix any import issues

### **Key Differentiation from My Original Approach**

After reading all suggestions, I'm adjusting my approach in these ways:

1. **Check existing completeness first** - Don't assume we need to build from scratch
2. **The κ definition is more subtle** - It's not just "binary on recΔ", it's specifically "+1 only on recΔ _ _ (delta _)"
3. **MuCore might not need changes** - The lemmas might already exist in `Termination.lean`
4. **The finite/infinite bridge lemmas are crucial** - These enable the `mu_lt_eq_diff` proof

### **Confidence Assessment Update**

- **Termination_Lex.lean is already complete:** 85% (up from my original 0%)
- **We can achieve full SN proof today:** 95% (up from 90%)
- **The mathematical approach is sound:** 100% (unanimous agreement)

### **Immediate Next Step**

```bash
# The single command that tells us everything:
lake build OperatorKernelO6.Meta.Termination_Lex 2>&1 | grep -E "(error|sorry)"
```

If this returns empty, we're essentially done and just need to clean up the project structure!

### **The Meta-Lesson**

The convergence of all AI analyses on the same solution (lexicographic with κ-drop only on rec_succ) strongly suggests this is not just **a** correct approach, but **the** correct approach. The mathematical necessity of avoiding `rec_succ_bound` forces this specific solution.


────────────────────────────────────────

# Plan Overview # 4

What I found (tight summary)
Your intended SN route is the lexicographic measure
𝜇
^
(
𝑡
)
:
=
(
𝜅
(
𝑡
)
,
 
𝜇
(
𝑡
)
)
μ
​
 (t):=(κ(t),μ(t)) with lex order:
κ strictly drops only on recΔ … (delta _), and μ strictly drops on each of the other seven rules. This is exactly the design your consolidation notes describe and the curated harness already sketches (call drop_left for R_rec_succ, drop_right elsewhere). all_suggestions

The current red builds come from two places:

mu_lt_eq_diff (the μ-drop for R_eq_diff) is called in the harness but not exported by the active MuCore—your own notes say to add it back via the principal-tower domination pipeline (no tricky product lemma). all_suggestions

A previously used lemma shape opow_mul_lt_of_exp_lt : β<α → 0<γ → ω^β*γ < ω^α is mathematically false in general (counterexample 
𝛽
=
0
,
𝛼
=
1
,
𝛾
=
𝜔
β=0,α=1,γ=ω); every plan that leans on that “positivity-only” version is brittle. Your docs steer us to the sum-domination route instead (the one with termA_le, termB_le, omega_pow_add3_lt, then lift by 
𝜔
4
ω 
4
 ). all_suggestions

All the building blocks for the safe proof are already in your repo (or verbatim in earlier drafts), including the payload bounds:

termB_le and the 3-term payload squeeze culminating in
payload_bound_merge : ω^3*(x+1) + (ω^2*(x+1) + 1) ≤ ω^(x+5) (exact statements present). Termination_C Termination

The general ordinal scaffolding—le_omega_pow, finite-offset bridges like add2_plus1_le_plus3/add3_plus1_le_plus4, and the strict/weak monotonicity of 
𝛼
↦
𝜔
𝛼
α↦ω 
α
 —is already used throughout your termination drafts. Termination Termination_Legacy Termination

The lex harness shape is correct: LexNatOrd := Prod.Lex (·<·) (·<·), WF via WellFounded.prod_lex and pullback via InvImage.wf. These are standard mathlib facts (lexicographic WF + WF pullback). 
Department of Mathematics
Lean Language

For ordinals we’re safe to rely on: well-foundedness of < on ordinals, normality of 
𝜔
−
ω 
−
  (strictly increasing in exponent), and opow_add. 
Lean Language
Proof Assistants Stack Exchange

Why your current errors happen (and why they’ll disappear)
R_eq_diff branch broken
The harness calls MuCore.mu_lt_eq_diff but the symbol isn’t exported in the active MuCore. Your own “next steps” explicitly say: expose termA_le, termB_le, and the final mu_lt_eq_diff built via principal-add + 
𝜔
_
ω 
_
  monotonicity. Once we reinstate it, the eq-diff branch collapses by right lex with κ equal (exactly as your harness expects). all_suggestions

Impossible κ-equal subgoals in merge-with-recΔ traces
Earlier attempts hard-forced “κ equal” for every non-rec-succ rule, which clashes whenever the term exposed by a rule happens to be a recΔ …. Your own curated harness avoids this: for the seven rules it tries μ-drop first with κ equality (true in the shapes those rules produce); if κ doesn’t match, the lex still drops because μ drops anyway. No need to assert κ equality where it’s not true. The prepared snippets in your notes adopt that exact pattern. Claude_SN

Bad ordinal lemma (the positivity-only opow_mul_lt_of_exp_lt)
That is not a mathlib lemma and the shape is false; it’s the source of unsolvable goals in your experimental MuCore. Your plan already removes it and replaces eq-diff with the sum-domination chain:

bound the merge payload by a single principal tower ω^(A+B+5)

multiply by ω^4 (for integrate) to reach ω^(A+B+9)

tack on the terminal “+1” and absorb under eqW’s top principal.
Those steps are exactly realized by the lemmas you’ve been collecting (see below). all_suggestions

The exact μ-drop we’ll (re)use for eqW_diff
Let 
𝐴
:
=
𝜇
(
𝑎
)
A:=μ(a), 
𝐵
:
=
𝜇
(
𝑏
)
B:=μ(b), 
𝐶
:
=
𝐴
+
𝐵
C:=A+B. Using your existing bounds:

termA_le: 
𝜔
3
⋅
(
𝐴
+
1
)
≤
𝜔
𝐴
+
4
ω 
3
 ⋅(A+1)≤ω 
A+4
  and
termB_le: 
𝜔
2
⋅
(
𝐵
+
1
)
≤
𝜔
𝐵
+
3
ω 
2
 ⋅(B+1)≤ω 
B+3
 . Termination_C

From those and finite-offset bridges, you already proved

yaml
Copy
Edit
payload_bound_merge :
  ω^3·(x+1) + (ω^2·(x+1) + 1) ≤ ω^(x+5)
(plug x := A and separately x := B inside the merge expansion; your notes instantiate it exactly). Termination_C

Therefore

𝜇
(
merge 
𝑎
 
𝑏
)
+
1
  
<
  
𝜔
 
𝐶
+
5
.
μ(merge ab)+1<ω 
C+5
 .
Multiply by 
𝜔
4
ω 
4
  (monotone, principal) and fold exponents with opow_add:

𝜇
(
integrate
(
merge 
𝑎
 
𝑏
)
)
  
=
  
𝜔
4
⋅
(
𝜇
(
merge 
𝑎
 
𝑏
)
+
1
)
+
1
  
<
  
𝜔
 
𝐶
+
9
+
1
  
=
  
𝜇
(
eqW 
𝑎
 
𝑏
)
.
μ(integrate(merge ab))=ω 
4
 ⋅(μ(merge ab)+1)+1<ω 
C+9
 +1=μ(eqW ab).
This is precisely the mu_lt_eq_diff lemma your harness wants—and it uses only your green-channel tools (principal additivity, exponent monotonicity, opow_add, finite offset bridges), all of which are already established in your drafts. Termination Termination_Legacy Termination

(Background support from mathlib: ordinals are well-founded; 
𝜔
−
ω 
−
  is a normal function (strictly increasing); and lexicographic products of WF relations are WF. These are the only external facts we need.) 
Lean Language
Proof Assistants Stack Exchange
Department of Mathematics

Step-by-step, concrete plan (copy this checklist)
A. Quarantine old branches (so they stop poisoning the build)

Exclude Termination_Legacy.lean and any “μ-only Measure” file from imports used by the final harness (keep them as archival refs only). This removes the rec_succ_bound dead-ends and the duplicate decls that your errors pointed to. all_suggestions

B. Finish MuCore (safe μ-lemmas only)
2) Export the payload bounds that are already present:

termB_le (and termA_le) — both are in your notes with exact proofs. Termination_C Termination

payload_bound_merge — the 3-term squeeze to 
𝜔
𝑥
+
5
ω 
x+5
 . Termination_C

(Re)introduce mu_lt_eq_diff (a b) via the sum-domination route above (no product lemma). Your consolidation shows the pattern and the ordinal bridges we need (le_omega_pow, add2_plus1_le_plus3, add3_plus1_le_plus4, opow_add, strict-mono of 
𝜔
_
ω 
_
 ). Termination Termination_Legacy Termination
(This is the one missing lemma the harness depends on.)

C. Keep one harness (lex) and wire every rule
4) Lex order + WF glue:
LexNatOrd := Prod.Lex (·<·) (·<·); WF by WellFounded.prod_lex … Ordinal.lt_wf, and pull back via InvImage.wf. (Standard Mathlib.) 
Department of Mathematics
Lean Language

5) κ design: 1-bit/flag that only distinguishes recΔ … (delta _) at the root (or the equivalent “depth bump” you already used). Keep your existing kappaD_drop_recSucc Nat proof for the strict drop on R_rec_succ.
Every other rule: do not force κ equality; simply use μ-drop lemmas (κ may coincidentally be equal by simp, that’s fine).
6) Per-rule closes (exactly as in your curated harness):

R_int_delta → μ-drop (mu_void_lt_integrate_delta) + κ equality by simp.

R_merge_void_left/right → μ-drop (mu_lt_merge_void_left/right).

R_merge_cancel → μ-drop (mu_lt_merge_cancel).

R_rec_zero → prefer μ-drop (mu_lt_rec_zero); κ non-increase is OK.

R_rec_succ → left lex via kappa_drop_recSucc.

R_eq_refl → μ-drop (mu_void_lt_eq_refl).

R_eq_diff → μ-drop using the newly reinstated mu_lt_eq_diff.
(These are exactly the “seven via μ, one via κ” routes you recorded.) all_suggestions

D. Hygiene
7) Ensure only one exported SN theorem (the lex harness), no duplicate builds. all_suggestions
8) #print axioms on the SN theorem should show no new axioms.
9) Do not reintroduce the positivity-only opow_mul_lt_of_exp_lt—your own notes classify it as unsafe; we don’t need it. all_suggestions

Why this is safe (and minimal)
Kernel unchanged (no rule edits). ✔️

κ decreases only on recΔ-succ; we never rely on κ elsewhere. ✔️

μ decreases on the other seven rules, including eqW_diff via the documented payload-to-principal pipeline (no right-add strictness, no product shortcut). ✔️
You already carry all the ordinal lemmas we need (or their exact patterns) in the repo drafts I cited; we just surface them from MuCore and use them. Termination_C Termination Termination_Legacy

WF uses the standard library items (lexicographic WF + pullback), whose existence and meaning are documented. 
Department of Mathematics
Lean Language

(Ordinal background: < on ordinals is well-founded; 
𝜔
_
ω 
_
  is normal/strictly increasing; opow_add available.) 
Lean Language
Proof Assistants Stack Exchange

Concrete “next 3 edits” I’d do first
MuCore: expose (or move into MuCore)
termA_le, termB_le, payload_bound_merge, then implement mu_lt_eq_diff along the sum-domination chain above. (Names and exact inequalities match your drafts.) Termination_C Termination

Harness: in Termination_Lex.lean ensure the R_eq_diff branch uses:

lean
Copy
Edit
have hμ := MuCore.mu_lt_eq_diff a b
have hk : kappa (…) = kappa (…) := by simp [kappa]  -- κ equal on both sides
exact drop_right hμ hk.symm
(Everything else already follows the 7×μ / 1×κ scheme you curated.) all_suggestions

Lake / imports: drop Termination_Legacy.lean and any “μ-only Measure” file from the build used by the final SN theorem. Keep only the lex harness exporting SN. 