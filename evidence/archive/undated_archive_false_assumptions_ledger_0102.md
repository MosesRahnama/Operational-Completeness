# False Assumptions Ledger (first pass scaffold)

Each entry: ID | Phase | Original Assumption | Where it appeared | Why it failed | Evidence/Counterexample | Status | Remediation/Replacement

- FA-001 | O6 | A single global lexicographic measure (κ, μ) suffices for all Step, even with duplication | Termination_* docs | Duplicate RHS breaks strict drop without stronger order | DualLex_Counterexample.md; Impossibility_Lemmas refs | Superseded | Hybrid termination via KO7 triple-lex + MPO
- FA-002 | O6 | Ordinal addition is strictly right-monotone for transport of < across + c | Various ordinal-toolkit notes | False for ordinals; right-add hazards documented | Expanded_Ordinal_Toolkit.md notes; mathlib lemmas | Superseded | Use opow/mul monotonic fragments; avoid right-add transport
- FA-003 | O6 | κ + k (fixed bump) ensures tie-breaking globally | Fails catalog | Counterexamples at δ shapes and merges | fails_central.md | Superseded | Per-branch analysis with κ-first lex gate; local proofs only
- FA-004 | KO4→O6 | Internality of the measure can be assumed | Early SN attempts | Internalizable measure couldn’t cover all rules | Termination_Consolidation.md | Superseded | InternallyDefinableMeasure class records base+flags; hybrid uses external wf where needed
- FA-005 | O6 | Global domination lemma for δ-substitutions | Termination drafts | Substitution breaks the global bound | docs and Lean comments | Superseded | Use δ-top two-case lemmas; local Star runners
