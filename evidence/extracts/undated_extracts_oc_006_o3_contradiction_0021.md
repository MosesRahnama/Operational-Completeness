Claim: OC-006
Source: C:\Users\Moses\OpComp\MUST_Review\O3-Moment.md
SourceLastWriteUtc: 2025-10-23T02:38:52.7570000Z

Summary Table extract:
  158: 
  159: ---
  160: 
  161: ## J.  Summary Table
  162: 
  163: | Attempt                   | Extra component | Core idea           | Show-stopper                 |
  164: | ------------------------- | --------------- | ------------------- | ---------------------------- |
  165: | μ only                    | μ (ordinal)     | One big ordinal     | False rec_succ bound         |
  166: | κ +1                      | κ (max)         | Small bump          | equality when n=δ m          |
  167: | κ +2/+3                   | κ (max)         | Bigger bump         | fails for nested δ           |
  168: | κ + μ                     | κ, μ            | let μ save tie      | needs false bound again      |
  169: | κ (+2) with helper lemmas | κ               | prove drop lemma    | inequality wrong when n=δ _  |
  170: | δ-flag                    | Boolean flag    | outer tie-breaker   | flag increases on merge-void |
  171: | **ρ + κ + μ**             | ρ counter       | count recSucc sites | *No blocker found yet*       |
  172: 
  173: ---
  174: 
  175: ## Next Action (green path)

Immediate Correction extract:
  220: re-evaluate the broader strategy.
  221: 
  222: =====IMMEDIATE CORRECTION=====
  223: 
  224: Before writing Lean code I triple-checked the algebra of the ρ-counter.
  225: Unfortunately the **duplication of `s` in `merge s …` breaks it**:
  226: 
  227: ρ(after) = ρ(before) – 1 + ρ(s)   because
  228: 
  229: • one problematic node disappears (–1)
  230: • an *extra* copy of `s` appears (+ρ(s))
  231: 
  232: If `s` itself contains any `recΔ … (δ …)` sub-nodes, then ρ(s) ≥ 1 and
  233: the net change is **≥ 0**.  In that case ρ does *not* strictly drop and
  234: the lexicographic triple fails.
  235: 
  236: So a plain “count-the-bad-nodes” measure cannot work; the merge rule
  237: creates arbitrarily large positive swings.
  238: 
