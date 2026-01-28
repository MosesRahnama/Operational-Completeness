Test file.
# Turing Cheat-Sheet

> Visual, compact, no fluff. If it can’t loop, it can’t cope.

## 0) What is "Turing-complete"?
A model that can simulate a universal Turing machine given unbounded memory and time.

---

## 1) Universal Turing Machine (UTM)
A machine U that takes (program, input) for any Turing machine M and simulates M(input).

ASCII sketch
```
+---------+    program p    +-------------------+
|  UTM U  | <-------------- |  description of M |
|         |  input  x  ---> |  and input  x     |
+---------+                  +-------------------+
```

Tiny interpreter-style pseudocode
```
function UTM(p, x):
  state := init(p)
  while true:
    (state, action) := step(p, state, x)
    if action == HALT: return state.output
```

---
## 2) Turing-computable function
A function f: N^k -> N that some TM computes. Equivalent to lambda-definable and general recursive.

Example: parity (odd=1, even=0)
```
function parity(n):
  acc := 0
  while n > 0:
    acc := 1 - acc
    n := n - 1
  return acc
```

Example: Collatz steps (partial function)
```
function collatz_steps(n):
  steps := 0
  while n != 1:
    if n % 2 == 0: n := n / 2
    else: n := 3*n + 1
    steps := steps + 1
  return steps
```

---
## 3) Control flow primitives
- Unconditional jump: `goto L`
- Conditional branch: `if cond then goto L`
- Loop: repeat while condition holds
- Recursion: function calls itself until base case
Either loop or recursion suffices.

Samples
```
# Unconditional jump (infinite loop)
L1: a := a + 1; goto L1

# Conditional branch + loop (factorial)
function fact(n):
  acc := 1
  while n > 0:
    acc := acc * n
    n := n - 1
  return acc

# Recursion (factorial)
function factR(n):
  if n == 0: return 1
  return n * factR(n-1)
```

---
## 4) Finite-State Machines (FSM)
- Finite states only. No unbounded memory.
- Recognize exactly the regular languages.
- Cannot count arbitrarily or match nested parentheses.

Sample A: email-ish NFA (sketch)
```
start --letters+--> atLocal --@--> atAt --letters+--> atDomain --dot--> dot --letters+--> accept
```

Sample B: DFA for even number of 1s
```
State S_even: on '1' -> S_odd; on '0' -> S_even
State S_odd:  on '1' -> S_even; on '0' -> S_odd
Accepting: S_even
```

---
## 5) Strong normalization (cannot express non-termination)
- A calculus is strongly normalizing if no infinite reduction exists.
- Example: simply typed lambda calculus (STLC) is strongly normalizing.
- Consequence: by itself, STLC is **not** Turing-complete.

Tiny STLC-flavored example
```
// Church numerals and addition terminate in STLC
// No general recursion operator without adding a fixpoint (Y)
```

Add a fixpoint (Y combinator) + unbounded data and you reintroduce non-termination -> TC.

---
## 6) Minimal TC examples

### SUBLEQ (one-instruction computer)
Memory: unbounded array of integers.
Instruction: subleq a b c  // M[b]=M[b]-M[a]; if M[b]<=0 jump to c
Sketch program: decrement to zero
```
// assume cells: A=n, ONE=1, TMP=0, PC=...
loop: subleq ONE, A, done
      subleq ONE, TMP, loop  // jump back via TMP<=0

// done: ...
```

### Rule 110 (cellular automaton)
A 1D CA with a simple local rule that can simulate a cyclic tag system.
Use long initial tapes to encode programs.

### Game of Life
2D CA known to be TC; logic gates and TMs are built from gliders.

---
## 7) Non-examples (not TC)
- Pure FSMs (regular languages only).
- Bounded-memory machines.
- Strongly normalizing calculi without a fixpoint or equivalent.

## 8) Quick tests for TC
- Unbounded memory?
- Conditionals and iteration (or recursion)?
- Ability to emulate a known TC core (e.g., 2-counter machine, SUBLEQ)?

## 9) Pointers for deeper study
- Turing, 1936.
- Böhm–Jacopini, 1966: structured control is enough.
- Minsky: 2-counter machines are universal.

End. If it can loop forever, it can make your CPU cry.
