Claim: KO7-004
Source: C:\Users\Moses\OneDrive - Mina Analytics Inc\Desktop\papers\1_OperatorKO7\OperatorKO7_Complete_Documentation.md
SourceLastWriteUtc: 2026-01-27T16:00:11.8094929Z

Extract:
  101: | R_rec_zero :  b s, Step (rec b s void) b
  102: | R_rec_succ :  b s n, Step (rec b s (delta n)) (app s (rec b s n))
  103: | R_eq_refl :  a, Step (eqW a a) void
  104: | R_eq_diff :  a b, Step (eqW a b) (integrate (merge a b))
  105: 
  106: /-- Reflexive-transitive closure of the kernel step relation `Step`. -/
  107: inductive StepStar : Trace  Trace  Prop
  108: | refl :  t, StepStar t t
  109: | tail :  {a b c}, Step a b  StepStar b c  StepStar a c
  110: 
  111: /-- Normal forms for the full kernel relation: no outgoing `Step`. -/
  112: def NormalForm (t : Trace) : Prop :=   u, Step t u
  113: 
