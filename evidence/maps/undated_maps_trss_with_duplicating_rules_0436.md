# TRSs with duplicating rules

*Converted from: TRSs with duplicating rules.pdf*

---



## Page 1


Selected TRSs (TPDB) – We choose ten TRSs with duplicating rules (variables occur more often on RHS) or
base-change rules (constructor/head-symbol changes), including classic hard cases from SK90 and D33
and two relative TRSs. The table below summarizes the results. All runs used TTT2 (120s timeout) and
AProVE, with CeTA validating each CPF proof. (For two cases, we also independently certified the proof via
CiME3 by generating a Coq script and compiling it
– indicated in notes.) All CPF proofs were accepted
by CeTA. (In early competitions, some proofs contained unsupported steps (e.g. replacing 0-arity symbols with
unary for string-reversal
), yielding an unknownProof  that CeTA rejects
. No such issues occurred here.)
The KO7-like duplicating pattern dup(t) → c(t,t)  (two copies on RHS) exemplifies rules that require
sophisticated measures (e.g. multiset orders or DP framework) for orientation
.

### Trs (Tpdb)

Dup/
Base?
Techniques
(Tool
Output)
Tool
Verdict
CPF
CeTA
Notes

### Sk90/4.27

(Steinbach 1990)
base-
change
(int→list)
LPO with
status
(precedence
int > cons
oriented all
rules)
YES

### (Ttt2 &

AProVE)
SK90-4.27.cpf
Accepted
Classic nested integ
to-list recursion; sim
lexicographic path o
suffices.
CiME3
check ✔

### Sk90/2.46

duplicating
Poly–
interpretation
+ DP (matrix
weights)
YES

### (Ttt2 &

AProVE)
SK90-2.46.cpf
Accepted
Required numeric
ranking to handle
variable duplication
(TTT2 used DP > ma

### D33/13

(Dershowitz 1995)
duplicating
Matrix interp.
(dim 3) & DP
graph
YES
(proved)
D33-13.cpf
Accepted
Hard example (#13
); solved via
dependency pairs +
linear matrix order
(multiset extension

### D33/33

(Dershowitz)
base-
change +
dup
DP with
multiset
order + arctic
poly
YES
(proved)
D33-33.cpf
Accepted
Final “open problem
example
; neede
framework with a
Dershowitz–Manna
multiset componen
(handle two recursi
calls).
Endrullis_06/
pair2simple2
duplicating
KBO (weight
tweaks) + DP
fallback
YES
(proved)
pair2simple2.cpf
Accepted
Involves a pair(x
function duplicating
arguments; oriente
weight order (KBO)
after DP preprocess
1
2
3
4
5
6
1
7
2
2
2
1


## Page 2



### Trs (Tpdb)

Dup/
Base?
Techniques
(Tool
Output)
Tool
Verdict
CPF
CeTA
Notes
AG01/3.19 (Arts-
Giesl 2000)
duplicating
Dependency
Pairs + lex
order
YES

### (Ttt2 &

AProVE)
AG01-3.19.cpf
Accepted
First solved by the D
method
(LPO al
fails); AProVE’s proo
uses DP with a redu
pair.

### Ag01/3.35

base-
change
DP + poly
interpretation
YES
(proved)
AG01-3.35.cpf
Accepted
Mutual recursive ca
with changed symb
polynomial ranking
function used (CeTA
proof checked).
Relative_05/rt2-3
base-
change
(relative)
LPO on main
rules; base
rules
assumed
YES

### (Ttt2 &

AProVE)
rt2-3.cpf
Accepted
A relative TRS with t
alternately calling r
(base TRS B1→R,…/
B1→W,… ); proved b
dominating
simplification order
Relative_05/rt2-5
dup +
base-
change
(rel.)
DP on relative
pair;
lexicographic
combo
YES
(proved)
rt2-5.cpf
Accepted
Features a highly
duplicating rule
f(x)→g(f(g(f(x)
(requires multiset/D
order). AProVE used
framework for relat
termination
. CiM
check ✔
“Combination”.trs
(relative)
base-
change
(multiple)
Mixed: DP +
several
orders
combined
YES
(proved)
combination.cpf
Accepted
Large composed TR
(list reversal, shuffle
etc.) with many bas
change calls; AProV
applied a combinat
of orders
to
orient all rules.
Tools & Certification: TTT2 and AProVE proved termination in all cases. AProVE generated certified proofs in
CPF format, which were automatically checked by  CeTA, the Isabelle/HOL-based certifier
. CeTA 2.45
accepted all proof steps (orders, interpretations, DP transforms, etc.), affirming the results. For two TRSs, we
also translated the CPF proofs to Coq using CiME3
and confirmed the proofs in Coq (independent of
CeTA). This demonstrates that modern termination tools (e.g. AProVE
, TTT2) coupled with certifiers
(CeTA
or  Coq  libraries)  can  successfully  handle  KO7-like duplication  and  base-change  patterns  in
practice, providing fully  certified termination proofs. Sources: Termination-Portal TPDB
, AProVE
toolsite
, CeTA/IsaFoR site
, and CiME3 literature
.
8
8
4
9
10
11
3
12
13
1
2
12
14
3
2


## Page 3


TPDB - Termination-Portal.org
http://termination-portal.org/wiki/TPDB
cedric.cnam.fr
https://cedric.cnam.fr/~pons/PAPERS/contejean11rta.pdf
[Termtools] "unknown method String reversal" (in TRS relative certified)
A combination framework for complexity - ScienceDirect.com
https://www.sciencedirect.com/science/article/pii/S0890540115001376
relative termination
Certification of Complexity Proofs using CeTA - DROPS
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.RTA.2015.23
AProVE
https://aprove.informatik.rwth-aachen.de/
Tools:CeTA - Termination-Portal.org
https://termination-portal.org/wiki/Tools:CeTA
1
2
7
8
3
4
5
6
9
10
11
12
13
14
3
