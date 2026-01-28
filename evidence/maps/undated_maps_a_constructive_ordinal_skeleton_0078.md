# A) Constructive Ordinal (CNF) — Skeleton and Full Lemma List

Goal: Replace Ordinal-based μ with a computable ordinal surrogate using Cantor Normal Form (CNF) over base ω, enabling removal of `noncomputable`.

## Core data model

- Type: CNF ordinal (finitary) over ω
  - CNF := list of (exp, coeff) pairs with invariants: strictly descending exponents, coeff > 0, exponents and coeffs are natural numbers.
  - Notation: ⟦Σ i < k. ω^(eᵢ) * cᵢ⟧ with e₀ > e₁ > … > eₖ₋₁, cᵢ ∈ ℕ+, eᵢ ∈ ℕ.

## Total order and operations (computable)

- cmp_cnf : CNF → CNF → Ordering
- le_cnf, lt_cnf: induced from cmp_cnf
- norm_cnf : CNF → CNF (enforce invariants)
- add_cnf : CNF → CNF → CNF
- mul_cnf : CNF → CNF → CNF
- opowω_cnf : CNF → CNF

All functions are structurally recursive on lists; `norm_cnf` enforces canonicality (merge equal exponents, drop zero coeffs).

## Key properties to prove (full names match planned Lean lemmas)

- cnf_wf : WellFounded lt_cnf
- cnf_total : IsStrictTotalOrder CNF lt_cnf
- cnf_norm_idem : ∀ x, norm_cnf (norm_cnf x) = norm_cnf x
- cnf_norm_eq : ∀ x, x ≈ y (extensional equality) → norm_cnf x = norm_cnf y

Monotonicity and arithmetic laws:
- cnf_add_norm_left  : ∀ x y, add_cnf (norm_cnf x) (norm_cnf y) = add_cnf x y |> norm_cnf
- cnf_mul_norm_left  : ∀ x y, mul_cnf (norm_cnf x) (norm_cnf y) = mul_cnf x y |> norm_cnf
- cnf_add_le_add_right : ∀ x y z, le_cnf x y → le_cnf (add_cnf x z) (add_cnf y z)
- cnf_mul_le_mul_left  : ∀ x y z, lt_cnf 0 z → le_cnf x y → le_cnf (mul_cnf z x) (mul_cnf z y)
- cnf_opowω_le_opowω_right : ∀ x y, le_cnf x y → le_cnf (opowω_cnf x) (opowω_cnf y)
- cnf_opowω_lt_opowω_right : ∀ x y, lt_cnf x y → lt_cnf (opowω_cnf x) (opowωω_cnf y)

Bridging to existing Ordinal-based lemmas (drop-in replacements):
- principal_add_omega0_opow_cnf — analogue of principal_add_omega0_opow
- add_one_le_of_lt_cnf, lt_add_one_iff_cnf — successors bridges in CNF setting

## Replacement map for current code

In `Termination_KO7.lean` and toolkit modules, replace usages:
- Ordinal.opow_le_opow_right → cnf_opowω_le_opowω_right
- opow_lt_opow_right (local) → cnf_opowω_lt_opowω_right
- mul/add monotonicity: use cnf_* variants
- principal_add_omega0_opow → principal_add_omega0_opow_cnf

## Module and namespacing

- New module: `OperatorKernelO6.Meta.CNFOrdinal`
  - Types/defs: CNF, cmp_cnf, le_cnf, lt_cnf, norm_cnf, add_cnf, mul_cnf, opowω_cnf
  - Lemmas: as listed above with the exact names

All functions/lemmas will be computable (no classical choice).
