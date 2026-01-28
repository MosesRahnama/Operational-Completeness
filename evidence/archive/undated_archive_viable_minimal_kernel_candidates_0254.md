# VIABLE MINIMAL-KERNEL CANDIDATES

*Converted from: VIABLE MINIMAL-KERNEL CANDIDATES.pdf*

---


VIABLE MINIMAL-KERNEL CANDIDATES (all assume β /
ann / id / void rules already fixed)
VIABLE MINIMAL-KERNEL CANDIDATES (all assume β / ann / id / void rules already fixed)
– All options preserve cancellation negation provided complement-uniqueness lemma is proved.
IMMEDIATE HIGH-RISK PROOFS (uncertain even in O-6) P1  Complement-Uniqueness: ∀x y z, merge x z →* void ∧ merge y z →* void ⇒ x
= y. Needed for sound negation, Boolean laws.
P2  Global Confluence with eqW + recΔ: Must enumerate and join every peak (β, ann, rec₀, rec₁, eq rules). Failure breaks Truth predicate
(nf unique).
P3  Internal Derivability Conditions D1–D3: Formalise substitution inside Trace, show Prov encodes modus-ponens and Σ₁-reflection.
Mandatory for Gödel II.  No prior literature in a terminating TRS; feasibility open.
(if any of these three collapse, Gödel II collapses with them.)
TIMELINE ESTIMATE Optimistic 2–3 weeks is plausible only if: • you automate critical-pair generation, • re-use existing Lean termination
packages, • and keep proof objects highly mechanical.
Otherwise typical completion times remain months.
NEXT ACTION Pick O-6, focus sequentially:
“O-4”  (4 OPERATORS) Core: void, delta, integrate, merge Extra rewrites: none How to get arithmetic: Church-style δ-chains, iteration
via self-applied integrate/merge gadgets (no dedicated recursor). Equality: encode by exhaustive δ-unrolling inside a merge loop.
Risks:  • Strong-normalisation doubtful once self-application is allowed. • No clean internal equality ⇒ diagonal construction
becomes meta only. Status: adequate for Robinson-Q-level arithmetic; Gödel I achievable meta-theoretically, Gödel II unlikely
without extra operator.
1.
“O-5A” (5 OPERATORS: recursion) Core: void, delta, integrate, merge, recΔ New rules: Rrec₀  recΔ b s void      → b Rrec₁  recΔ b s
(delta n) → s (recΔ b s n) Arithmetic & bounded search become primitive-recursive inside the system. Equality: still needs meta
traversal → diagonal inside still blocked. SN proof: by δ-height measure. Confluence: trivial new peaks (recΔ vs ann). Suitability:
Gödel I can be completed once an equality macro is derived (heavy). Gödel II still needs derivability conditions.
2.
“O-5B” (5 OPERATORS: equality) Core: void, delta, integrate, merge, eqW New rules: Req₁  eqW a b → void                        if nf a = nf
b Req₂  eqW a b → integrate(merge nfa nfb)    otherwise (canonical order) Equality internal, diagonal easy; arithmetic forced to use
very inefficient search (no recursor). SN proof: by multiset(nf-size, eqW flag). Confluence: join peaks eqW/ann, eqW/β. Suitability:
Gödel I done, Gödel II needs primitive recursion for provability search → missing.
3.
“O-6”  (6 OPERATORS)  [recommended] Core: void, delta, integrate, merge, recΔ, eqW Rules: Rrec₀, Rrec₁, Req₁, Req₂ (+ existing).
Properties: • Arithmetic, bounded search, primitive recursion → recΔ • Internal decidable equality → eqW • Diagonal & Σ₁-provability
internal, proofs remain SN/confluent (measures: δ-height + nf-size). Everything required for both incompleteness theorems can be
carried inside the reduction system.
4.
“O-6*” (keep 6, add discretionary lam/app privately) Extended lam/app only for metaprogramming; erased before extraction.  Kernel
unchanged; keeps axiom-free property.
5.
prove P2 (confluence) → ensures framework stability;
1.
prove P1 (negation) → validates logic layer;
2.
attack P3 (derivability) → unlocks second incompleteness.
3.
