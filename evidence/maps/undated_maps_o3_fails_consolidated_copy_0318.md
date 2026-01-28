# OperatorKernelO6 — Consolidated Failure Report (o3_fails_consolidated.md)

_Last compiled: 2025-08-14_

## 0. Scope & Sources
Summarises the three post-mortem files (`fails.md`, `fails_2.md`, `fails_3.md`) and the running `PROJECT_LOG.md` under the **Strict Execution Contract**.  No new claims are introduced; every bullet matches at least one source sentence.  Items that still need confirmation are listed under **§ 7 Verify**.

---
## 1. The Single Hard Rule
```
recΔ b s (δ n)  →  merge s (recΔ b s n)   (R_rec_succ)
```
Any termination measure must strictly decrease across this rule while tolerating:
* duplication of `s` on the RHS;
* arbitrary nesting of `δ` in `n`.

All failed attempts share the mistake of ignoring **both** duplication _and_ nested-δ effects.

---
## 2. Catalogue of Failed Strategies
| # | Strategy (first appearance) | Essence | Root Cause |
|---|-----------------------------|---------|------------|
| 1 | μ-only ordinal ("rec_succ_bound") | Single transfinite measure | Key inequality false; required right-add & absorption without proof |
| 2 | κ = max-depth + 1 | Constant bump | Ties when `n = δ _` (nested-δ land mine) |
| 3 | κ with bigger constants (+2, +3, …) | Constant escalation | Any finite bump neutralised by one more nested δ |
| 4 | (κ, μ) lexicographic | Delegate tie to μ | Re-imports the false μ inequality (circular) |
| 5 | κ(+2) with helper lemmas | Attempted bound ≤ base+1 | Bound wrong in δ-branch; Lean reduces to `⊢ False` |
| 6 | δ-flag + (κ, μ) triple | Boolean discriminator | Flag increases on merge-void; lex order breaks |
| 7 | ρ = count of bad nodes | Additive counter | Merge duplicates `s`, so ρ can increase |
| 8 | κ depth-only (0 on merge) with (κ, μ) lex | Nat–first lexicographic pair | κ increases on `merge→t` and `rec_zero`; lex fails |

(_Sources: fails.md §1-7; fails_2.md §1-6; fails_3.md §2-8_)

---
## 3. Recurrent AI Reasoning Failures
1. **Wishful Mathematics** – assuming inequalities that “should” hold.
2. **Shape Blindness** – ignoring the δ/non-δ split of `n`.
3. **Duplication Amnesia** – forgetting that merge duplicates its subterm.
4. **Constant Fetishism** – believing +k bumps solve structural ties.
5. **Problem Shuffling** – lexicographic layers that just re-express the false bound.
6. **Premature Celebration** – declaring success before the nested-δ test.
7. **Local Repair Syndrome** – patching symptoms (replace `=` by `≤`) without re-proving.
8. **Lexicographic Confusion** – assuming the second coordinate can rescue an increased first coordinate.

(_Sources: fails_2.md §🔍/§📝; fails_3.md §9/§11._)

---
## 4. Early-Warning Checklist (extracted)
* Test `n = δ m` **first**; if the measure ties, stop.
* Inspect every rule for **duplication**; additive counters usually fail.
* Never use ordinal right-add or absorption without explicit hypotheses `ω ≤ p`.
* Treat any `sorry` or axiom in a core inequality as a red alert.
* Be sceptical of claims that a finite constant bump fixes the issue.

---
## 5. Viable Unexplored Directions (consensus)
* **Multiset Path Ordering (MPO/RPO)** – duplication robust; head-symbol precedence `recΔ > merge` gives immediate drop.
* **Sized Types / Semantic Labelling** – encode δ-depth in the type; rec_succ drops size, merge copies size unchanged.
* **Kernel change** (least preferred) – redesign the rule to avoid duplication.

---
## 6. Lessons Recorded in PROJECT_LOG.md
* Multiple builds confirm the same failure pattern; κ(+2) branch still breaks on nested δ.
* `Termination_Lex.lean` currently **incomplete**; diagnostics list unsolved goals and timeouts.
* Recent fix in `Termination_C.lean` achieves κ-drop for rec_succ by making κ=0 on merges and 1 on `recΔ … (δ _)`, _but_ this increases κ in merge-to-recΔ targets, so the full step-decrease theorem is still open.  (_Log 2025-08-14 00:05Z & subsequent_)

---
## 7. Verify — Items Requiring Confirmation
* Whether the newly added κ-only measure in `Termination_C.lean` can be extended to **all** merge rules when the target is `recΔ …` (possible counter-example not yet formalised).
* The claim in some EOD reports that `Termination_Lex.lean` was “85 % green” – current build diagnostics show unsolved goals; percentage needs recalculation.
* Any mention that `SN_Final.lean` compiles “green” conflicts with latest `lake build` failure in PROJECT_LOG (line 23). Confirm current status.

---
## 8. One-Line Closing Motto
> _“If an argument ignores duplication **or** nested δ, assume it fails until proven otherwise.”_
*** End of consolidated report ***
