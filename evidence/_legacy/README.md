# Evidence Archive

This folder contains 440+ files documenting AI failures at the `rec_succ` termination problem.

## Structure

```
evidence/
├── EVIDENCE_MAP.md           # Maps paper claims (P1-P6) to evidence files
├── AI_FAILURES_DOCKET.md     # Comprehensive failure documentation (1,253 lines)
├── transcripts/              # Raw AI conversation logs
│   ├── 10-27-25-Gemini-pro-2.5.md
│   ├── 10-30-25-Opus-4.1-strict_verification.md
│   ├── 11-01-25-DeepSeek-R1.md
│   └── ...
├── lean_graveyard/           # Failed termination proof attempts
│   └── Consolidated_Meta_Termination_Patch.md (5,748 lines)
└── analysis/                 # Cognitive autopsies and diagnostics
    ├── Detailed_Reasoning_Autopsy.md
    ├── The_Exact_Failure_Moment.md
    ├── Why_AI_Fails_At_RecSucc_Logic.md
    └── ...
```

## Key Evidence Files

| File | Lines | Content |
|------|-------|--------|
| `O3-Moment.md` | ~200 | O3 catches own flaw in real-time |
| `opus_fails_consolidated.md` | ~150 | 10-strategy failure table |
| `The_Ultimate_Failure.md` | 43 | "Let there be Two" confession |
| `WrongPredictions.md` | 176 | 17 wrong predictions with file:line anchors |
| `Consolidated_Meta_Termination_Patch.md` | 5,748 | Complete Lean code graveyard |

## The Eight Horsemen of AI Reasoning

Recurring failure patterns documented across all models:

1. **Wishful Mathematics** - Assuming inequalities "should" hold
2. **Shape Blindness** - Ignoring LHS/RHS structural differences
3. **Duplication Amnesia** - Forgetting s appears twice after reduction
4. **Constant Fetishism** - Believing +k bumps solve structural problems
5. **Problem Shuffling** - Moving difficulty to helper lemmas that fail identically
6. **Premature Celebration** - Declaring success before checking all branches
7. **Local Repair Syndrome** - Patching symptoms without addressing root causes
8. **Lexicographic Confusion** - Misapplying lex ordering rules
