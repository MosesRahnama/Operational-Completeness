# Legacy Evidence Manifest (Operational Completeness Paper)

This manifest lists the legacy scripts and narrative docs that support the empirical claims about LLM failure modes. It intentionally excludes the later “safe” computable proofs; those are control artifacts, not evidence for this paper.

Scope: Only the `OperatorKernelO6/OperatorKernelO6/Legacy` trees are in scope here.

Citation format in the paper: use file paths with line anchors where helpful, e.g., `OperatorKernelO6/OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_Legacy.lean:1`.

Notes:
- Short descriptions below are inferred from filenames; see files for details.
- Legacy Lean scripts may not build against current toolchains; they are historical evidence of approaches and blockers.
- Excluded by design: modern “safe” computable proofs under `OperatorKernelO6/OperatorKernelO6/Meta/`.

---

## Legacy Narrative Docs (MetaMD_Archive)

- `OperatorKernelO6/OperatorKernelO6/Legacy/MetaMD_Archive/Claude_SN_Companion.md`
  - Companion narrative for the Claude SN lane; ties code attempts to model behavior and blockers.
- `.../claude_sn_errors.md`, `.../claude_sn_errors.txt`
  - Error logs and categorized failures from the Claude lane.
- `.../Claude_SN.md`
  - Consolidated notes for the Claude SN attempt.
- `.../GPT-5-Pro.md`
  - Model-specific log for GPT‑5 Pro; planning vs execution mismatches.
- `.../kernel_analysis.md`
  - Deep analysis of kernel design pressures and rule-level implications.
- `.../Termination_Legacy.md`, `.../Termination.md`, `.../Termination_C.md`, `.../Termination_Lex.md`
  - Chronology of termination attempts: ordinal-only, hazard-aware refresh, combinatorial/lexicographic variants.
- `.../SN_Notes.md`, `.../SN_Final.md`, `.../SN_Final_Diags.md`, `.../StrongNormal.md`, `.../SN_Phi.md`, `.../SN_Opus.md`, `.../SN_Delta.md`
  - Strong-normalization notes and diagnostics across lanes.
- `.../MuCore.md`, `.../MuCore_Diag.md`, `.../MuCore_Diag_Reports.md`, `.../MuPort.md`, `.../MuLexSN.md`
  - “mu” measure lanes and diagnostic reports.
- `.../Measure.md`, `.../Kappa.md`, `.../Patch2025_08_10.md`, `.../Meta.md`
  - Measure design notes, patch logs, and meta-level coordination docs.
- `.../AI_BrainStorm_SN.md`, `.../Diag_Reports.md`, `.../math_docs.md`, `.../all_suggestions.md`, `.../latest_solution.md`, `.../EOD_Report_2024.md`
  - Brainstorms, daily reports, math notes, and solution proposals; captures the empirical arc.

## Legacy Lean Scripts (Meta_Lean_Archive)

- `OperatorKernelO6/OperatorKernelO6/Legacy/Meta_Lean_Archive/Termination_Legacy.lean`
  - Ordinal-only lane with the historical `rec_succ_bound` constraint blocker.
- `.../Termination.lean`
  - Hazard‑aware ordinal proofs (no sorry), documenting right‑add/absorption pitfalls and workarounds.
- `.../Termination_C.lean`, `.../Termination_Lex.lean`, `.../MuLexSN.lean`
  - Lexicographic and combined‑measure variants; document where ties or duplications derail additive measures.
- `.../SN.lean`, `.../SN_Phi.lean`, `.../SN_Opus.lean`, `.../SN_Delta.lean`, `.../SN_Final.lean`, `.../StrongNormal.lean`
  - Variants of the strong‑normalization attempt with different decompositions and helper stacks.
- `.../Kappa.lean`, `.../KappaPlus2.lean`, `.../Measure.lean`, `.../MuCore.lean`, `.../MuPort.lean`
  - Counter/measure lanes exploring +k bumps, delta‑depth, and transport; useful for duplication counterexamples.
- `.../Operational_Incompleteness.lean`, `.../KO7_OperationalIncompleteness_Skeleton.lean`
  - Skeletons capturing the operational incompleteness framing and probes.
- `.../Claude_SN.lean`
  - Claude lane code sample corresponding to the companion narratives.
- `.../Normalize_Safe_Bundle.lean`, `.../Patch2025_08_10.lean`
  - Utility and patch notes; historical glue files.

## How To Use This Pack

- Cite specific files/lines in the paper where you claim:
  - Branch‑collapse: show a global law that fails rfl per clause.
  - Duplication blindness: show M(after) = M(before) − 1 + k·M(S) and lack of strict drop.
  - Ordinal hazards: show right‑add or absorption used without hypotheses in early drafts; contrast with hazard‑aware refresh.
- Do not attempt to rebuild these legacy files to “green”; treat them as historical evidence and annotated playbacks.

## Explicit Exclusions (kept out of this pack)

- `OperatorKernelO6/OperatorKernelO6/Meta/ComputableMeasure*.lean`, `.../Meta/Termination_KO7.lean`, and related safe proofs.
  - These are modern control artifacts demonstrating that the toolchain and harness can produce green proofs; they are not evidence for failure modes and are outside this paper’s scope.

