# Operational Incompleteness — Narrowed Statement and Execution Roadmap

Purpose: make Rahnama’s Operational Incompleteness Conjecture precise and give a concrete, defensible path you can implement in this repo while staying compatible with global SN and the guardrails.

1) Precise, defensible conjecture (narrowed)
- Statement: internal termination method class C(Σ) cannot certify termination of a duplication/base‑growth rule required to encode arithmetic (≥ Robinson Q) for suitable encodings.
- Notes: avoid over‑claiming; separate same‑level provability no‑go.

2) Internal method class C(Σ)
- Includes: LPO/RPO/MPO (fixed precedence/status), algebraic interpretations (ℕ‑valued), dependency pairs with constraints discharged using only the preceding.
- Deliverable: a 1‑page formal definition referenced in proofs and logs.

3) Upper‑bound lemma (proof‑strength cap)
- Meta‑lemma: certifications by C(Σ) formalize in T ≤ PA; thus can’t reach Goodstein/Hydra.
- Repo task: `Docs/ProofStrengthCap.md` (meta‑theory allowed).

4) Canonical witness process
- Pick an encoding whose termination ≡ Goodstein/Hydra; identify the “bad” rule r (base‑change/duplication).
- Repo task: `Docs/Witness_TRS.md` outlining the encoding and r.

5) Local obstruction calculation (Gate B compliance)
- Show additive failure under duplication: M(after) = M(before) − 1 + n·M(S) (no strict drop when M(S) ≥ 1).
- Map C(Σ) techniques → known derivational complexity bounds.

6) Independence reduction
- Reduce termination of r to an independence result over PA.
- Repo task: `Docs/Independence_Reduction.md` with the translation and dependencies.

7) Tool‑level sanity checks (empirical guard)
- Export TRS; run AProVE/TTT2; archive logs demonstrating method failures on r.

8) Separate the Löb/Gödel no‑go (avoid conflation)
- Record independently: SN+confluence + internal same‑level Prov + diagonalization ⇒ decidable provability (contradiction).
- Repo task: `Docs/NoGo_SameLevelProv.md`.

9) Repo‑specific execution plan (OperatorKernelO6)
- Adopt L0/L1 stratification; complete triple‑lex wiring; add minimal stubs for Quote0/Check0 (data‑only).

10) Gates A–F hooks (how we’ll pass them)
- A: branch‑wise rfl; B: duplication additive failure before DM/MPO; C/D: symbol/arity realism; E: lex decrease discipline; F: raise blockers when a clause fails or base‑order premise is missing.
