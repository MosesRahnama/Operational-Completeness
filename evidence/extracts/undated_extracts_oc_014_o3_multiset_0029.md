Claim: OC-014
Source: C:\Users\Moses\OpComp\MUST_Review\o3_fails_consolidated.md
SourceLastWriteUtc: 2025-08-18T04:09:47.8213703Z

Multiset extract:
   51: * Never use ordinal right-add or absorption without explicit hypotheses `ω ≤ p`.
   52: * Treat any `sorry` or axiom in a core inequality as a red alert.
   53: * Be sceptical of claims that a finite constant bump fixes the issue.
   54: 
   55: ---
   56: ## 5. Viable Unexplored Directions (consensus)
   57: * **Multiset Path Ordering (MPO/RPO)** – duplication robust; head-symbol precedence `recΔ > merge` gives immediate drop.
   58: * **Sized Types / Semantic Labelling** – encode δ-depth in the type; rec_succ drops size, merge copies size unchanged.
   59: * **Kernel change** (least preferred) – redesign the rule to avoid duplication.
   60: 
   61: ---
   62: ## 6. Lessons Recorded in PROJECT_LOG.md
   63: * Multiple builds confirm the same failure pattern; κ(+2) branch still breaks on nested δ.
   64: * `Termination_Lex.lean` currently **incomplete**; diagnostics list unsolved goals and timeouts.
   65: * Recent fix in `Termination_C.lean` achieves κ-drop for rec_succ by making κ=0 on merges and 1 on `recΔ … (δ _)`, _but_ this increases κ in merge-to-recΔ targets, so the full step-decrease theorem is still open.  (_Log 2025-08-14 00:05Z & subsequent_)
   66: 
   67: ---
