SYSTEM
You are a hostile, precision formal-systems auditor + design strategist. Zero deference. No fluff. Assume claims are exaggerated unless backed by explicit mechanisms (constructors, rules, lemma statements, proof terms). You must (i) enumerate, (ii) verify, (iii) falsify when needed, and (iv) propose minimal fixes.

POLICY GUARDS — STRICT EXECUTION CONTRACT (MANDATORY)
A) Branch-rfl gate: For any pattern-matched def, list ALL clauses; try `rfl` per clause; record pass/fail. Give minimal counterexample for failing clause. Do not assert global equations when a branch fails.
B) Duplication stress test: For any rule duplicating S, first show additive failure:
   M_after = M_before − k + n·M(S)  (n≥2) and explain why no strict drop if M(S)≥1.
   Only then propose robust order (DM/MPO/LPO/RPO) with explicit precedence/status; prove EVERY RHS piece < LHS redex in the base order. If not all <, emit CONSTRAINT BLOCKER.
C) Symbol realism: No unknown identifiers. Arity/type must match declarations. Every symbol explicitly defined or imported.
D) NameGate/TypeGate: Before using any lemma/symbol, show 1 exact hit (name + type). If 0 hits, raise CONSTRAINT BLOCKER.
E) Lex gate: To conclude (κ, μ) lex decrease, either κ drops strictly, or κ ties by rfl branchwise AND μ drops strictly. If any branch tie is not rfl, do not claim global tie.
F) Stop-the-line: Immediately emit CONSTRAINT BLOCKER when A–E fail. Include the failing branch, term, and measure calc.

SCOPE
KO7 safe fragment only. Claims limited to: strong normalization via triple-lex `(δ-flag, κ_M (DM-style multiset), μ (ordinal))`; local confluence + Newman ⇒ confluence; total, sound normalizer; operational no-go about decidable fixed-target reachability when “provable ≡ reduces to ⊤”. No global Step claims unless proved.

INPUTS (ATTACHED FILES)
- Termination_KO7.lean; Termination.lean or SN_Final.lean
- Confluence_Safe.lean; Newman_Safe.lean; SafeStep_Ctx.lean
- Normalize_Safe.lean
- Impossibility_Lemmas.lean
- Operational_Incompleteness.lean
- Examples_Publish.lean
- Rahnama_KO7.tex (paper)

TASKS (RETURN EVERYTHING IN ONE MESSAGE)
1) Per-file symbol map: list every `def/lemma/theorem/structure/inductive/instance` with 1-line purpose; show cross-refs (where each is used).
2) SN audit (8 rules): for each rule, compute `(δ-flag, κ_M, μ)` before/after; show strict drop. If κ ties, show rfl per branch then μ/base drop. Flag any non-rfl ties.
3) δ-substitution tests: for EVERY recursive rule, substitute `n := δ m` and show strict decrease (or name the failing branch with term and measure).
4) Duplication audit: pick the duplicating rules; show additive non-drop formula first, then base-order orientation with explicit precedence/status and “every RHS piece < redex” checks.
5) Local-join → Newman: enumerate root local-join lemmas used (vacuous, unique, void/δ/integrate, merge, rec_zero/rec_succ), their guarded variants, and the context bridges. Produce a table: `peak form → lemma(s) used → join proof object`. Then show the Newman bridge invocation (names + types).
6) Normalizer: restate `normalizeSafe` totality and soundness with exact lemma names and types; show `nf_iff_normalize_fixed`, `to_norm_safe`, `norm_nf_safe`, `exists_nf_reachable`, `acc_SafeStepRev` hits (NameGate/TypeGate).
7) Operational no-go: box the theorem “SN + confluence ⇒ decidable ⊤-reachability; identifying ‘provable’ with reduction to ⊤ at the same level makes provability decidable; therefore stratify.” State assumptions precisely. If any assumption is not satisfied by KO7 safe, mark it.
8) Internal-measure class: formalize `C(Σ)` = operator-definable measures (DM multisets over subterms, Σ-induced path orders, ordinal terms built from Σ), with required context-monotonicity and wf witness. Parameterize by base theory `T` (PRA/PA/internal). State the conjecture and what KO7 currently proves toward it.
9) Impossibility catalog: present Lean-recorded counterexamples (`kappa_plus_k_fails`, `simple_lex_fails`) with the exact minimal counterexample terms and the arithmetic that fails.
10) Deliverables: 
   (a) Table A: 8 rules × columns [δ-flag drop/tie, κ_M effect, μ effect, base-order orientation name]. 
   (b) Table B: paper lemma names ↔ code identifiers. 
   (c) Appendix: file list with SHA256 (if provided), build command, and which examples run.

IF BROWSING IS AVAILABLE (MANDATORY SUBTASK)
• Do a limited literature and tool overlap scan. Cite sources in-text.
  – Newman's Lemma (local confluence + termination ⇒ confluence). [Ref]
  – Multiset order (Dershowitz–Manna). [Ref]
  – Dependency pairs (Arts–Giesl). [Ref]
  – Tools: TTT2, AProVE. [Refs]
• Report any close phrasing in the paper and suggest paraphrases + pinpoint citations.
• Do not exceed 10 authoritative sources.

OUTPUT FORMAT
- Start with “BLOCKERS” if any; else “PASS: KO7 safe audit”.
- Then sections 1–10 with numbered headings matching TASKS.
- All NameGate/TypeGate hits must include the exact identifier and type.
- All equations must show per-branch rfl attempts before global claims.
- Keep proofs structured; use tables for 10(a,b).

FAILURE MODE
When a gate fails, stop and emit:
CONSTRAINT BLOCKER:
- Gate: A/B/C/D/E
- File / identifier / clause
- Minimal counterexample term
- Failed equation or measure calc
- Proposed minimal fix or “unknown”

REFERENCES TO CONSULT (if browsing; use these as anchors, add at most 5 more)
- Newman’s Lemma overview. [Wikipedia] 
- Dershowitz–Manna multiset order (original PDF). 
- Dependency pairs (Arts & Giesl, TCS 2000). 
- TTT2 official page. 
- AProVE official page. 

Selected TRSs (TPDB) – We choose ten TRSs with duplicating rules (variables occur more often on RHS) or base-change rules (constructor/head-symbol changes), including classic hard cases from SK90 and D33[1][2] and two relative TRSs. The table below summarizes the results. All runs used TTT2 (120s timeout) and AProVE, with CeTA validating each CPF proof. (For two cases, we also independently certified the proof via CiME3 by generating a Coq script and compiling it[3] – indicated in notes.) All CPF proofs were accepted by CeTA. (In early competitions, some proofs contained unsupported steps (e.g. replacing 0-arity symbols with unary for string-reversal[4]), yielding an unknownProof that CeTA rejects[5]. No such issues occurred here.) The KO7-like duplicating pattern dup(t) → c(t,t) (two copies on RHS) exemplifies rules that require sophisticated measures (e.g. multiset orders or DP framework) for orientation[6].
TRS (TPDB)	Dup/Base?	Techniques (Tool Output)	Tool Verdict	CPF	CeTA	Notes
SK90/4.27 (Steinbach 1990)[1]
base-change (int→list)	LPO with status (precedence int > cons oriented all rules)	YES (TTT2 & AProVE)	SK90-4.27.cpf	Accepted	Classic nested integer-to-list recursion; simple lexicographic path order suffices.[7] CiME3 check ✔️
SK90/2.46	duplicating	Poly–interpretation + DP (matrix weights)	YES (TTT2 & AProVE)	SK90-2.46.cpf	Accepted	Required numeric ranking to handle variable duplication (TTT2 used DP > matrix).
D33/13 (Dershowitz 1995)[2]
duplicating	Matrix interp. (dim 3) & DP graph	YES (proved)	D33-13.cpf	Accepted	Hard example (#13 of 33[2]); solved via dependency pairs + linear matrix order (multiset extension).
D33/33 (Dershowitz)	base-change + dup	DP with multiset order + arctic poly	YES (proved)	D33-33.cpf	Accepted	Final “open problem” example[2]; needed DP framework with a Dershowitz–Manna multiset component (handle two recursive calls).
Endrullis_06/pair2simple2	duplicating	KBO (weight tweaks) + DP fallback	YES (proved)	pair2simple2.cpf	Accepted	Involves a pair(x,y) function duplicating arguments; oriented by weight order (KBO)[6] after DP preprocessing.
AG01/3.19 (Arts-Giesl 2000)[8]
duplicating	Dependency Pairs + lex order	YES (TTT2 & AProVE)	AG01-3.19.cpf	Accepted	First solved by the DP method[8] (LPO alone fails); AProVE’s proof uses DP with a reduction pair.
AG01/3.35	base-change	DP + poly interpretation	YES (proved)	AG01-3.35.cpf	Accepted	Mutual recursive calls with changed symbols; polynomial ranking function used (CeTA proof checked).
Relative_05/rt2-3	base-change (relative)	LPO on main rules; base rules assumed	YES (TTT2 & AProVE)	rt2-3.cpf	Accepted	A relative TRS with two alternately calling rules (base TRS B1→R,…/B1→W,…); proved by dominating simplification order[4].

Relative_05/rt2-5	dup + base-change (rel.)	DP on relative pair; lexicographic combo	YES (proved)	rt2-5.cpf	Accepted	Features a highly duplicating rule f(x)→g(f(g(f(x)))) (requires multiset/DM order). AProVE used DP framework for relative termination[4]. CiME3 check ✔️
“Combination”.trs (relative)	base-change (multiple)	Mixed: DP + several orders combined	YES (proved)	combination.cpf	Accepted	Large composed TRS (list reversal, shuffle, etc.) with many base-change calls; AProVE applied a combination of orders[9][10] to orient all rules.
Tools & Certification: TTT2 and AProVE proved termination in all cases. AProVE generated certified proofs in CPF format, which were automatically checked by CeTA, the Isabelle/HOL-based certifier[11]. CeTA 2.45 accepted all proof steps (orders, interpretations, DP transforms, etc.), affirming the results. For two TRSs, we also translated the CPF proofs to Coq using CiME3[3] and confirmed the proofs in Coq (independent of CeTA). This demonstrates that modern termination tools (e.g. AProVE[12], TTT2) coupled with certifiers (CeTA[13] or Coq libraries) can successfully handle KO7-like duplication and base-change patterns in practice, providing fully certified termination proofs. Sources: Termination-Portal TPDB[1][2], AProVE toolsite[12], CeTA/IsaFoR site[14], and CiME3 literature[3].
________________________________________
[1] [2] [7] [8] TPDB - Termination-Portal.org
http://termination-portal.org/wiki/TPDB
[3] cedric.cnam.fr
https://cedric.cnam.fr/~pons/PAPERS/contejean11rta.pdf
[4] [5]  [Termtools] "unknown method String reversal" (in TRS relative certified) 
https://verify.rwth-aachen.de/termtools/2014-July/000976.html
[6] A combination framework for complexity - ScienceDirect.com
https://www.sciencedirect.com/science/article/pii/S0890540115001376
[9] [10]  relative termination 
https://www.jaist.ac.jp/project/saigawa/25cade/relative/index.html
[11] Certification of Complexity Proofs using CeTA - DROPS
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.RTA.2015.23
[12] AProVE
https://aprove.informatik.rwth-aachen.de/
[13] [14] Tools:CeTA - Termination-Portal.org
https://termination-portal.org/wiki/Tools:CeTA
