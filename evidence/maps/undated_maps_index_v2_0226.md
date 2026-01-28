# Documentation Index

- Canonical submission index: `../Submission_Material/md/INDEX.md`

- Universal rules (canonical): `../Submission_Material/md/1.Universal_Rules.md`
- Ordinal toolkit (canonical): `../Submission_Material/md/2.Expanded_Ordinal_Toolkit.md`
- Termination consolidation (canonical): `../Submission_Material/md/3.Termination_Consolidation.md`
- Hybrid termination summary (publishable): `Hybrid_Termination.md`
- Full termination development notes: `Termination_Documentation.md`
- Operator Kernel overview: `Kernel_Documentation.md` (see also HTML/PDF variants)

## Orientation summary (snapshot)

- Base orientation: r1, r3, r7, r8 (direct base drops)
- Per-piece orientation: r2, r5, r6 (per_piece_base_lt witnesses)
- Duplication r4: oriented via DM/MPO/lex witnesses

## Safe local-join coverage (snapshot)

- δ-guarded roots: `Delta_SafePairs_Exhaustive_add`, `Delta_SafePairs_Exhaustive_mul`
- Context lifting: wrappers in `Confluence_Safe.lean` (e.g., `localJoin_ctx_*`)

## Readability addenda

- Dual-lex counterexample (canonical): `../Submission_Material/md/DualLex_Counterexample.md`
- 1→0 δ walk-through (recΔ succ): see the rec-succ lex drop comments in `Meta/Termination.lean` and the `(κ, μ)` lex strategy notes in `3.Termination_Consolidation.md`.
- Relation diagram (conceptual): `Step ∨ Admin` ⟶ transitive-reflexive closure `RelStar`; one-step Goodstein/Hydra simulations embed via small lemmas `simulate_*_relStar`.
