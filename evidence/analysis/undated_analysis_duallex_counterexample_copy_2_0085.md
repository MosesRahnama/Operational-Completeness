# Minimal dual-lex counterexample (why kappa + k fails globally)

This note explains why a global measure of the form (κ + k, μ) does not strictly decrease for all rules.

- Duplicating rule r4 (mul (s x) y → add y (mul x y)) duplicates the subterm S := y on the right.
- Additive measure argument: after removing one redex, the multiplicity M changes as
  M(after) = M(before) - 1 + M(S), which is not a strict drop when M(S) ≥ 1.
- Therefore, a naive (κ + k) tie with fixed k cannot ensure a global strict decrease.

In the repo, the formal P2 lemmas showing this are in `OperatorKernelO6/Meta/Operational_Incompleteness_Skeleton.lean` (namespace `P2`):
- `dup_additive_failure`: exhibits the additive non-drop under duplication.
- `not_strict_drop`: packages the counterexample to show the global decrease fails.

Robust fix (used in the safe fragment): move to a multiset-of-weights order (Dershowitz–Manna) or an MPO/RPO with explicit precedence/status so that each RHS piece is strictly smaller than the removed LHS redex in the base order.
