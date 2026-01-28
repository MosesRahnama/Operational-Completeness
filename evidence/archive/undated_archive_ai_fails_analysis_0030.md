# AI Fails Analysis — Consolidated Report (O3 + Opus)

This document consolidates the two prior summaries:
- o3_fails_consolidated.md
- opus_fails_consolidated.md

It preserves their structure where useful, merges overlapping points, and flags divergences. The goal is a single quick-reference for failure modes, checks, and open items under the Strict Execution Contract.

---

## 0. Scope & Sources
- Sources: prior “fails” notes (`fails.md`, `fails_2.md`, `fails_3.md`) and `PROJECT_LOG.md` as referenced by both O3 and Opus summaries.
- Contract framing: A–G gates (branch rfl, duplication, symbol realism, lex gate, hazards, stop-the-line, probes).
- This file introduces no new claims; each bullet appears in at least one of the two inputs.

---

## 1. The Single Hard Rule

```
recΔ b s (delta n)  →  merge s (recΔ b s n)   (R_rec_succ)
```
- Must strictly decrease any termination measure.
- Stressors: duplication of `s` on RHS; arbitrary nested `delta` in `n`.
- Shared conclusion: ignoring duplication or nested-`delta` leads to failure.

---

## 2. Catalogue of Failed Strategies (Merged)

| # | Strategy | Essence | Root Cause |
|---|----------|---------|------------|
| 1 | Ordinal-only (μ) with “rec_succ_bound” | One big ordinal measure | Key inequality is false; improper right-add/absorption |
| 2 | κ = max-depth + 1 | Constant bump | Ties when `n = delta _` (nested-delta) |
| 3 | Bigger constants (+2, +3, …) | Constant escalation | Any finite bump neutralized by deeper nesting |
| 4 | (κ, μ) lex | Delegate ties to μ | Reintroduces the false ordinal bound |
| 5 | κ(+2) with helpers | Repair lemma | Bound wrong in delta-branch; Lean exposes `False` goal |
| 6 | Boolean flag + (κ, μ) | Outermost discriminator | Flag increases on merge-void; lex breaks |
| 7 | κ = count “bad nodes” | Additive counter | Merge duplicates `s`; κ can increase |
| 8 | κ depth-only + lex | Nat-first pair | κ increases on merge/rec_zero in some branches |

Notes: O3 presents the table tersely; Opus complements with concrete examples and counter-derivations.

---

## 3. Recurrent AI Reasoning Failures (Merged)
1. Wishful mathematics: assuming inequalities that “should” hold.
2. Shape blindness: ignoring the `delta`/non-`delta` split for `n`.
3. Duplication amnesia: forgetting merge duplicates subterms.
4. Constant fetishism: believing +k fixes structural ties.
5. Problem shuffling: lex layers that just move the blocker.
6. Premature celebration: claiming success before the `n = delta m` test.
7. Local repair syndrome: swapping `=` for `≤` without re-proving premises.
8. Lex confusion: claiming second-coordinate rescue after first coordinate increases.

---

## 4. Early-Warning Checklist
- Test `n = delta m` first; if measure ties/increases, stop.
- Inspect every rule for duplication; additive counters usually fail.
- Do not use ordinal right-add/absorption without explicit hypotheses (e.g., `ω ≤ p`).
- Treat any `sorry`/admit in core inequalities as a red alert.
- Be skeptical that any fixed +k resolves nested-delta ties.

---

## 5. Viable Unexplored / Candidate Directions
- Multiset/Path Ordering (DM/MPO/RPO): duplication-robust under proper precedence/status; premise “each RHS piece < removed redex.”
- Sized types / semantic labeling: encode delta-depth into types; rec_succ strictly drops size.
- Kernel change (least preferred): redesign to avoid duplication.

---

## 6. Project Log Highlights (Merged)
- Multiple builds show the same failure pattern; κ(+2) still breaks on nested `delta`.
- `Termination_Lex.lean`: incomplete; unsolved goals and timeouts persist.
- `Termination_C.lean`: κ-drop for rec_succ achieved by flagging, but κ increases in some merge→rec targets; global decrease remains open.
- Claims like “85% green” are inconsistent with latest diagnostics; need recalculation.

---

## 7. Items Requiring Verification (Merged)
1. Whether κ-only measures extend to all merge→rec targets (counterexample suspected).
2. Reconcile “green” claims with current `lake build` output for `Termination_Lex.lean` and `SN_Final.lean`.
3. kappaTop + μTop proposals: completeness requires the missing μTop definition and per-branch checks.
4. DM/MPO practicality: confirm an actual orientation that proves all per-rule premises.

---

## 8. Differences Between O3 and Opus Summaries
- O3 is concise/table-oriented for quick scanning; Opus adds mathematical detail and counter-examples.
- Both agree on the core blocker (R_rec_succ) and the duplication/nested-delta trap.

---

## 9. Conclusion
- 7/8 rules: straightforward.
- 1 rule (R_rec_succ): defeats simple/additive/constant-bump approaches.
- Robust orientation (DM/MPO) or sized types may work but require nontrivial machinery.
- Operational takeaway: if an approach ignores duplication or nested-delta, assume failure until rigorously disproven.

> “If an approach ignores duplication OR nested delta, it will fail.”

---

## Appendix: Provenance
- O3 source: OperatorKernelO6/OperatorKernelO6/Meta_md/Archive/o3_fails_consolidated.md
- Opus source: OperatorKernelO6/OperatorKernelO6/Meta_md/Archive/opus_fails_consolidated.md
