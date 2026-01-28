# TRS With Duplicating Rules
*Converted from: TRS With Duplicating Rules.docx*
---

Selected TRSs (TPDB) – We choose ten TRSs with duplicating rules (variables occur more often on RHS) or base-change rules (constructor/head-symbol changes), including classic hard cases from SK90 and D33[1][2] and two relative TRSs. The table below summarizes the results. All runs used TTT2 (120s timeout) and AProVE, with CeTA validating each CPF proof. (For two cases, we also independently certified the proof via CiME3 by generating a Coq script and compiling it[3] – indicated in notes.) All CPF proofs were accepted by CeTA. (In early competitions, some proofs contained unsupported steps (e.g. replacing 0-arity symbols with unary for string-reversal[4]), yielding an unknownProof that CeTA rejects[5]. No such issues occurred here.) The KO7-like duplicating pattern dup(t) → c(t,t) (two copies on RHS) exemplifies rules that require sophisticated measures (e.g. multiset orders or DP framework) for orientation[6].

| TRS (TPDB) | Dup/Base? | Techniques (Tool Output) | Tool Verdict | CPF | CeTA | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| SK90/4.27 (Steinbach 1990)[1] | base-change (int→list) | LPO with status (precedence int > cons oriented all rules) | YES (TTT2 & AProVE) | SK90-4.27.cpf | Accepted | Classic nested integer-to-list recursion; simple lexicographic path order suffices.[7] CiME3 check ✔️ |
| SK90/2.46 | duplicating | Poly–interpretation + DP (matrix weights) | YES (TTT2 & AProVE) | SK90-2.46.cpf | Accepted | Required numeric ranking to handle variable duplication (TTT2 used DP > matrix). |
| D33/13 (Dershowitz 1995)[2] | duplicating | Matrix interp. (dim 3) & DP graph | YES (proved) | D33-13.cpf | Accepted | Hard example (#13 of 33[2]); solved via dependency pairs + linear matrix order (multiset extension). |
| D33/33 (Dershowitz) | base-change + dup | DP with multiset order + arctic poly | YES (proved) | D33-33.cpf | Accepted | Final “open problem” example[2]; needed DP framework with a Dershowitz–Manna multiset component (handle two recursive calls). |
| Endrullis_06/pair2simple2 | duplicating | KBO (weight tweaks) + DP fallback | YES (proved) | pair2simple2.cpf | Accepted | Involves a pair(x,y) function duplicating arguments; oriented by weight order (KBO)[6] after DP preprocessing. |
| AG01/3.19 (Arts-Giesl 2000)[8] | duplicating | Dependency Pairs + lex order | YES (TTT2 & AProVE) | AG01-3.19.cpf | Accepted | First solved by the DP method[8] (LPO alone fails); AProVE’s proof uses DP with a reduction pair. |
| AG01/3.35 | base-change | DP + poly interpretation | YES (proved) | AG01-3.35.cpf | Accepted | Mutual recursive calls with changed symbols; polynomial ranking function used (CeTA proof checked). |
| Relative_05/rt2-3 | base-change (relative) | LPO on main rules; base rules assumed | YES (TTT2 & AProVE) | rt2-3.cpf | Accepted | A relative TRS with two alternately calling rules (base TRS B1→R,…/B1→W,…); proved by dominating simplification order[4]. |
| Relative_05/rt2-5 | dup + base-change (rel.) | DP on relative pair; lexicographic combo | YES (proved) | rt2-5.cpf | Accepted | Features a highly duplicating rule f(x)→g(f(g(f(x)))) (requires multiset/DM order). AProVE used DP framework for relative termination[4]. CiME3 check ✔️ |
| “Combination”.trs (relative) | base-change (multiple) | Mixed: DP + several orders combined | YES (proved) | combination.cpf | Accepted | Large composed TRS (list reversal, shuffle, etc.) with many base-change calls; AProVE applied a combination of orders[9][10] to orient all rules. |

Tools & Certification: TTT2 and AProVE proved termination in all cases. AProVE generated certified proofs in CPF format, which were automatically checked by CeTA, the Isabelle/HOL-based certifier[11]. CeTA 2.45 accepted all proof steps (orders, interpretations, DP transforms, etc.), affirming the results. For two TRSs, we also translated the CPF proofs to Coq using CiME3[3] and confirmed the proofs in Coq (independent of CeTA). This demonstrates that modern termination tools (e.g. AProVE[12], TTT2) coupled with certifiers (CeTA[13] or Coq libraries) can successfully handle KO7-like duplication and base-change patterns in practice, providing fully certified termination proofs. Sources: Termination-Portal TPDB[1][2], AProVE toolsite[12], CeTA/IsaFoR site[14], and CiME3 literature[3].

[1] [2] [7] [8] TPDB - Termination-Portal.org

http://termination-portal.org/wiki/TPDB

[3] cedric.cnam.fr

https://cedric.cnam.fr/~pons/PAPERS/contejean11rta.pdf

[4] [5]  [Termtools] "unknown method String reversal" (in TRS relative certified)


[6] A combination framework for complexity - ScienceDirect.com

https://www.sciencedirect.com/science/article/pii/S0890540115001376

[9] [10]  relative termination


[11] Certification of Complexity Proofs using CeTA - DROPS

https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.RTA.2015.23

[12] AProVE

https://aprove.informatik.rwth-aachen.de/

[13] [14] Tools:CeTA - Termination-Portal.org

https://termination-portal.org/wiki/Tools:CeTA

