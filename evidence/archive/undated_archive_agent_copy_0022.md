# AGENT.md

PROJECT: OperatorMath Lean proofs.

RULES:
 Build and reason in axiom-free operator framework for arithmetic, logic, Gödel self-reference using inductive Trace with constructors void, delta, integrate, merge; emerge all from terminating confluent normalization—no external axioms, numerals, equality, Peano, classical like excluded middle. Define from scratch: theorems only, no lemmas; avoid sneaking Lean elements like Nat, DecidableEq, Bool/true/false, &&/|| operators, if-then-else, propext, classical, simp, rfl, by_cases, cases, injection, contradiction—or code incompletes into unprovable void.

CORE OBJECTS:
- Trace, constructors: void | delta | integrate | merge
- normalize (idempotent)
- FixpointWitness, fixedpoint_of_idempotent
- negation, Provable, Φ, G

TASK TYPES:
1. PLAN: Give numbered outline only (no code).
2. CODE: Give full Lean code block (no explanations outside the block).
3. SEARCH: List existing theorems/defs with (Name | File | Line | Short purpose).

FORMAT:
- Proof code block only:

theorem Name : <type> := by

- No extra commentary in code block.

IF BLOCKED:
Output:
CONSTRAINT BLOCKER
Needed theorem: <statement>
Reason: <why needed>

REMINDERS:
- Never invent lemma names.
- Never output `sorry`.