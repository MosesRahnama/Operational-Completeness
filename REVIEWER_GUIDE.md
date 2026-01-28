# Reviewer Guide

This guide is for fast verification and deep audit of the evidence archive.

## Quick path (15 to 30 minutes)

1. Read the paper PDF in `Paper/OpComp_new.pdf`.
2. Open the claim map in `evidence/maps/undated_maps_02_claim_map_0007.md`.
3. For each claim, open the linked extracts in `evidence/extracts`.
4. Use `evidence/INDEX.csv` to trace any file back to its source path.

## Full path (deep audit)

1. Read `evidence/maps/undated_maps_02_claim_list_0006.md` for the full claim list.
2. Read `evidence/docket` for failure summaries and method notes.
3. Verify transcripts in `evidence/transcripts`.
4. Review analyses in `evidence/analysis`.
5. Review failed proof attempts in `evidence/lean_graveyard`.

## What to verify

- The rec_succ duplication issue is shown in primary logs and extracts.
- The same failure appears across many models.
- The Strict Execution Contract is stated and used in tests.
- The evidence archive contains the stated classes of files.

## Evidence naming scheme

Each file name follows:

```
YYYY-MM-DD_category_slug_NNNN.ext
```

The source path and hash for each file are in `evidence/INDEX.csv`.

## Reference only

The KO7 repo is referenced only and not modified here.
Lean code is used only when needed, and only from:
`C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKO7\OperatorKO7_Complete_Documentation.md`
