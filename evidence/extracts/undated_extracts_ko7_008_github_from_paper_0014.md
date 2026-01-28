Claim: KO7-008
Source: C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKO7\Paper\Rahnama_KO7_Submission.tex
SourceLastWriteUtc: 2026-01-22T20:36:42.9139824Z

GitHub extract:
   32: \maketitle
   33: 
   34: \begin{abstract}
   35: This paper presents a minimal operator-only term rewriting system with seven constructors and eight reduction rules. The main contribution is a mechanically-verified proof of strong normalization for a guarded fragment using a novel triple-lexicographic measure combining a phase bit, multiset ordering (Dershowitz-Manna), and ordinal ranking. From strong normalization, a certified normalizer with proven totality and soundness is derived. Assuming local confluence (verified through critical pair analysis), Newman's Lemma yields confluence and therefore unique normal forms \emph{for the safe fragment}. Impossibility results showing that simpler measures, such as additive counters, polynomial interpretations, and single-bit flags, provably fail for rules with term duplication, are established. The work demonstrates fundamental limitations in termination proving for self-referential systems. A conjecture is stated: no \emph{relational} operator-only TRS can have its full-system termination proved by internally definable methods. Here ``relational'' is equivalent to ``capable of ordered computation'': systems with a recursor enabling iteration over successors, comparison, or sequential counting. Such recursors necessarily redistribute step arguments across recursive calls, defeating all additive termination measures. This structural limitation applies to any TRS expressive enough to encode ordered data. All theorems have been formally verified in a proof assistant. The Lean formalization is available at \url{https://github.com/MosesRahnama/OperatorKO7}.
   36: \end{abstract}
   37: 
   38: \section{Introduction}
   39: \label{sec:intro}
   40: This paper presents a minimal \emph{operator-only} rewrite calculus (\textbf{KO7}) where the object language contains only constructors and operators with rewrite rules. There are no binders, types, external axioms, or semantic predicates; the rules \emph{are} the semantics. The primary goals are: (i) a clean, duplication-robust proof of \emph{strong normalization} (SN); (ii) a \emph{certified normalizer} that always returns a normal form; (iii) \emph{unique} normal forms via Newman's Lemma under a local-confluence assumption; and (iv) a conjecture regarding the unprovability of termination for relational operator-only systems using internal methods.
   41: 
