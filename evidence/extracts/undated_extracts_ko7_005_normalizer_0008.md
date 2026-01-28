Claim: KO7-005
Source: C:\Users\Moses\OpComp\MUST_Review\Research.md
SourceLastWriteUtc: 2025-08-19T00:46:43.1944713Z

Normalizer extract:
    4: Overview of KO7 and Its Goals
    5: KO7 is a minimal “operator-only” term rewriting system (TRS) designed as a foundational kernel for logic or computation. In KO7, the object language has only a handful of constructors and operators (no binders, no types, no external axioms); the rewrite rules are the semantics  . The current version of KO7 consists of 7 base symbols (constructors) and 8 rewrite rules, all unconditional (though some have guard conditions)   .
    6: These rules handle operations like merging terms, recursive construction, equality checking (via	), and a
    7: special “delta” operation for differences  . The guiding goals for KO7 are ambitious yet clear  : (i) Strong Normalization (SN) – no infinite rewrite sequences, guaranteeing termination; (ii) a certified normalizer – an algorithm that always produces a normal form for any input term (with a machine-checked proof of its total correctness); and (iii) under an additional local confluence assumption, unique normal forms, so that the normalizer’s output is essentially canonical. In essence, KO7 aims to be a sound and terminating rewrite engine with potential for use in automated proof search or computation within a theorem prover. Despite its simplicity, KO7 touches on deep concepts in rewriting theory and logic, including the interplay of termination with decidability of reachability (more on this later). The work under review includes a complete formalization in Lean 4, meaning all theorems are mechanically proved within a proof assistant, adding high confidence in the results  .
    8: 
    9: Novel Contributions and Their Significance
   10: The KO7 project introduces several noteworthy contributions. Here we break down the most important and novel aspects of this work, explaining their significance:
   11: 
   12: •	Duplication-Robust Termination Proof: A core contribution is a rigorous proof that KO7 is strongly normalizing (terminating) even though some rules duplicate subterms	. Termination proofs for TRSs with duplicating rules are nontrivial, since a simple size measure can increase when a term is duplicated. The author devises a triple-lexicographic well-founded measure to prove that every
   13: rewrite step strictly decreases a certain measure of the term	. This measure	has three
   14: components ordered lexicographically: (1) a binary “phase” flag (to handle a change that occurs in
   15: one particular recursive rule), (2) a multiset extension of a rank function	(using the Dershowitz–
