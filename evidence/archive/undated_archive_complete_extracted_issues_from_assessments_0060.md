# COMPLETE EXTRACTION OF ALL ISSUES FROM ASSESSMENTS.MD

## ASSESSMENT 1 ISSUES

### Overall Architecture & Scope Claims Issues
1. **CRITICAL**: Paper claims and code are honest about limitations
2. **CRITICAL**: `not_localJoin_eqW_refl_when_kappa_zero` lemma explicitly proves that the full `Step` relation is NOT locally confluent
3. **ISSUE**: This contradicts any claim of global confluence for the full system

### Triple-Lex Termination Measure Issues
4. **POTENTIAL ISSUE**: The mixing of two different approaches (KO7 with DM multisets vs MPO with μ-first) suggests the proof isn't unified under a single measure

### Major Claims vs Reality Issues
5. **WARNING**: Confluence via Newman's lemma only for `SafeStep`, not full `Step`
6. **ISSUE**: The "operational no-go" theorem appears more philosophical than formally proven

### Measure Switching Problem
7. **FUNDAMENTAL ISSUE**: There's a fundamental issue with the termination proof in `Termination_KO7.lean`
8. **PROBLEM**: `HybridDec` isn't a single well-founded measure! It's a disjunction of two different measures
9. **ISSUE**: Each rule gets to "choose" which measure decreases (Some rules use KO7 triple-lex, others use MPO triple)
10. **VIOLATION**: This violates the fundamental principle of termination proofs - you need ONE measure that decreases on EVERY step
11. **ISSUE**: The code essentially admits defeat on finding a unified measure

### Confluence Gap Issues
12. **CRITICAL ISSUE**: `not_localJoin_eqW_refl_when_kappa_zero` explicitly proves that `eqW a a` is NOT locally confluent when `kappaM a = 0`
13. **ISSUE**: This means the full `Step` relation is NOT confluent
14. **ISSUE**: The `SafeStep` relation artificially excludes this case
15. **ISSUE**: The normalizer only works for the restricted `SafeStep`
16. **UNDERSTATED SEVERITY**: The paper mentions this but understates its severity
17. **SHOULD STATE**: The paper should more prominently state: "KO7 is NOT confluent as designed; we only prove confluence for an artificial subset."

### Phantom "Operational No-Go Theorem" Issues
18. **PROBLEM**: This "theorem" has no formal proof in the Lean code!
19. **ISSUE**: `Goodstein_NoSingleStep_Encode` just states that Goodstein sequences don't reduce in a single step
20. **ISSUE**: The broader philosophical claim about decidability is never formally proven
21. **ISSUE**: It's more of a conjecture or observation

### Additive Bump Impossibility Issues
22. **TRIVIAL PROOF**: The proof is trivial (adding k to both sides doesn't help with inequality)

### DM Multiset Component Issues
23. **PROBLEM**: The use of `∪` (union) instead of `+` (sum) for multisets means they're using multiset MAX, not multiset SUM
24. **ISSUE**: This fundamentally changes the termination argument
25. **ISSUE**: This isn't clearly explained in the paper

### Missing Context Closure Issues
26. **ISSUE**: Context closure is only for `SafeStep`, not the full `Step`
27. **ISSUE**: The paper doesn't clearly explain that context closure is restricted to the safe fragment

### Normalize Function Issues
28. **BAD**: It's marked `noncomputable`, meaning it can't actually be executed!
29. **ISSUE**: The "certified normalizer" is purely theoretical

### Newman's Lemma Implementation Issues
30. **ISSUE**: It only works under the assumption `locAll : ∀ a, LocalJoinAt a`, which we know is FALSE for the full system!

### Summary of Critical Issues
31. **ISSUE**: No unified termination measure - The code uses a hybrid of two different measures
32. **ISSUE**: Confluence only for artificial fragment - The full system is provably non-confluent
33. **ISSUE**: "Operational no-go theorem" is not proven - It's stated as philosophy, not mathematics
34. **ISSUE**: Normalizer is noncomputable - Can't actually be executed
35. **ISSUE**: Multiset union vs sum confusion - Mathematical details don't match standard DM
36. **ISSUE**: Guards are ad-hoc - The `SafeStep` restrictions feel reverse-engineered to make proofs work

### Verdict Issues
37. **NOT PROVEN**: Termination or confluence for the full KO7 system
38. **NOT FORMALLY PROVEN**: The "operational no-go theorem"
39. **NOT PROVIDED**: A single, unified termination measure
40. **OVERSTATED**: The paper should be titled: "A Partially Normalized Fragment of an Operator-Only Kernel"

## ASSESSMENT 2 ISSUES

### CONSTRAINT BLOCKER Issues
41. **CONSTRAINT BLOCKER**: The termination proof relies on HybridDec, which is a disjunction of two different measures
42. **ISSUE**: A termination proof requires a single, uniform well-founded relation that decreases for every reduction rule
43. **ISSUE**: The use of ∨ (OR) is not a valid way to combine measures
44. **ISSUE**: It indicates that no single measure was found that works for all the rules
45. **PROPOSED FIX NEEDED**: The entire termination proof needs to be refactored to use a single, consistent lexicographic measure for all 8 rules

### Duplication Audit Issues
46. **SUBTLE ISSUE**: The use of ∪ (multiset union) instead of + (multiset addition) is non-standard for the Dershowitz-Manna ordering
47. **ISSUE**: Not clearly justified
48. **ISSUE**: While it may be possible to prove termination this way, it deviates from the standard presentation and requires extra scrutiny

### Local-join → Newman Issues
49. **CONSTRAINT BLOCKER**: `not_localJoin_eqW_refl_when_kappa_zero` proves that the full Step relation is not locally confluent
50. **ISSUE**: The term eqW a a can reduce to both void and integrate (merge a a)
51. **ISSUE**: These two terms do not have a common reduct under SafeStepStar
52. **LIMITATION**: The claim of confluence must be restricted to the SafeStep relation

### Normalizer Issues
53. **ISSUE**: The function is defined using WellFounded.fix with classical logic, making it noncomputable
54. **ISSUE**: This means it's a proof of existence of a normal form, not an executable algorithm

### Operational no-go Issues
55. **ISSUE**: A search for "operational no-go" or similar terms in the file system did not reveal a formal proof
56. **ISSUE**: This is a philosophical claim rather than a formalized theorem

### Internal-measure class Issues
57. **ISSUE**: The project does not formalize a class of operator-definable measures as described in the prompt

### Impossibility catalog Issues
58. **ISSUE**: The file Impossibility_Lemmas.lean was not found in the directory listing (according to assessment 2)

## ASSESSMENT 3 ISSUES

### Duplication Issues (R4)
59. **ISSUE**: Paper claims RHS duplicates subterm S
60. **ISSUE**: No strict drop if M(y) ≥ 1

### Non-claims Issues
61. **ISSUE**: No global Step SN/confluence
62. **ISSUE**: Explicit non-local-confluence at eqW a a with κ=0

## PAPER↔CODE DIFF ISSUES

### Critical Paper vs Code Mismatch
63. **BLOCKER**: Paper Table 2 states rec (succ n) f → step (rec n f) (rec n f) (duplicating)
64. **ISSUE**: The artifact's rule is R_rec_succ : recΔ b s (delta n) ⟶ app s (recΔ b s n) (no duplication on RHS)
65. **FIX NEEDED**: Correct the paper's informal row to match the Lean LHS/RHS (no RHS duplication)
66. **ISSUE**: Do not reuse any global "duplication" argument for this rule

### Global Step Claims Issues
67. **ISSUE**: The paper hints at "Full Step per-rule decreases (Hybrid)" but admits no global aggregator
68. **ISSUE**: Non-local-confluence at eqW a a with κ=0
69. **FIX NEEDED**: Explicitly scope guarantees to SafeStep only

### Assessment 2 Paper↔Code Diff Issues
70. **BLOCKER**: Paper claims RHS duplicates; code does not
71. **ACTION NEEDED**: Fix rec-succ row in paper
72. **ISSUE**: Paper must correct to app s (recΔ b s n) and drop duplication rhetoric at rec-succ
73. **GUARD MISSING**: merge t t → t (unqualified) - Guard missing in paper
74. **GUARD MISSING**: eqW a a → void (unqualified) - Guard missing in paper
75. **RENAME NEEDED**: Paper uses mpo_drop_* but code uses drop_R_*
76. **ADD ALIAS**: δ-subst alias not explicit in paper

### Impact Issues
77. **ISSUE**: All "duplication-at-rec" arguments in the paper must be either rewritten to the δ-phase narrative or moved to the toy TRS

### Required Edits
78. **REQUIRED EDIT**: Replace the rec-succ row in the paper's rules table
79. **REQUIRED EDIT**: Change any mpo_drop_R_rec_succ to drop_R_rec_succ (δ-left)
80. **REQUIRED EDIT**: Delete or relabel "RHS duplicates subterm S" for KO7 safe

## ASSESSMENT 4 ISSUES

### Duplication Analysis Issues
81. **WRONG CALCULATION INITIALLY**: Assessment initially miscalculated the additive failure

### CRITICAL FINDINGS Issues
82. **ISSUE**: No unified termination measure - HybridDec is disjunctive, not a proper order
83. **ISSUE**: eqW reflexive peak at κ=0 blocks full confluence without additional mechanisms

### Section ? CONSTRAINT BLOCKER Issues
84. **CONSTRAINT BLOCKER**: Complete project state (all source files + last ≥ 5 log entries) needed
85. **ISSUE**: Current session lacks prerequisites, so every gate (A–F) would fail
86. **CONSTRAINT BLOCKER**: Actual Lean source contents for every file referenced in tasks 1–10 needed
87. **ISSUE**: Only small excerpts available; remaining modules required
88. **ISSUE**: Without the code cannot enumerate clauses, run rfl checks, or verify measures
89. **BLOCKING**: Full audit (tasks 1–10) blocked

## ASSESSMENT #XX ISSUES

### CONSTRAINT BLOCKER (D: NameGate/TypeGate) Issues
90. **CONSTRAINT BLOCKER**: The following identifiers are referenced but not present:
    - MetaSN.mu_void_lt_integrate_delta
    - MetaSN.mu_lt_merge_void_left
    - MetaSN.mu_lt_merge_void_right
    - MetaSN.mu_lt_merge_cancel
    - (likely) a μ-drop for eqW ("diff") as well
91. **ISSUE**: The Newman's lemma bridge symbol newman_safe is referenced but its declaration is not shown
92. **FIX NEEDED**: Expose/locate these lemmas in the Lean sources

### Strong Normalization Audit Issues
93. **BLOCKER**: Missing μ-right lemma μ(void) < μ(integrate (delta t))
94. **BLOCKER**: Missing μ-right strictness μ(t) < μ(merge void t)
95. **BLOCKER**: Missing μ-right μ(t) < μ(merge t t)
96. **BLOCKER**: Missing μ-right μ(void) < μ(eqW a a)
97. **BLOCKER**: Missing μ-right μ(integrate (merge a b)) < μ(eqW a b)
98. **ISSUE**: SN remains unsealed until μ-lemmas are surfaced

### δ-substitution Tests Issues
99. **ISSUE**: Minimal counterexample shows κ-profiles differ
100. **ISSUE**: Forbidding any global schematic equality across rec branches
101. **WARNING**: Do not assert global rec equalities

### Duplication Audit Issues
102. **ISSUE**: Additive non-drop: "−1 + M(t)" trick fails to ensure strictness when M(t) ≥ 1
103. **CONSTRAINT BLOCKER**: Needs explicit μ-drop lemmas to discharge "every RHS piece < LHS redex"

### Local-join → Newman Issues
104. **BLOCKER**: Bridge symbol newman_safe declaration not present in extracts

### Operational no-go Issues
105. **ISSUE**: Contingent on sealing SN (μ-lemmas) and exposing the Newman bridge

### Internal-measure class Issues
106. **ISSUE**: Missing μ-drop lemmas keep a few obligations open

### Deliverables Issues
107. **BLOCKER**: Need .tex text to map paper lemma ↔ code identifiers
108. **ISSUE**: Multiple files missing SHA256 hashes

### Structural Risk Issues
109. **RED FLAG**: eqW a a peak not fully neutralized at root in SafeStep
110. **ISSUE**: At eqW a a with kappaM a = 0 you have two distinct root rules
111. **ISSUE**: No direct root local-join lemma for the kappaM a = 0 peak without extra premises
112. **SYNCHRONIZATION RISK**: Substantial duplicate exports of the same sections exist
113. **ISSUE**: Can hide mismatches between the paper's table and code identifiers

## SUMMARY COUNT
Total Issues Extracted: 113

## SEVERITY CLASSIFICATION
- CONSTRAINT BLOCKERS: 10
- CRITICAL ISSUES: 5
- FUNDAMENTAL ISSUES: 2
- PROBLEMS: 6
- BLOCKERS: 12
- ISSUES: 68
- WARNINGS: 2
- FIX NEEDED: 4
- ACTION NEEDED: 2
- RED FLAGS: 1
- RISKS: 1