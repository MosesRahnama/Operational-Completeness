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

## Key evidence table

| Topic | File |
| --- | --- |
| O3 self-contradiction | `evidence/extracts/undated_extracts_oc_006_o3_contradiction_0021.md` |
| Gemini plum = 2 | `evidence/extracts/undated_extracts_oc_007_gemini_plum2_0022.md` |
| Gemini confession | `evidence/extracts/undated_extracts_oc_015_gemini_confession_0030.md` |
| DeepSeek contradiction | `evidence/extracts/undated_extracts_oc_009_deepseek_contradiction_0024.md` |
| Strategy failures | `evidence/extracts/undated_extracts_oc_011_strategy_failures_0026.md` |
| Strict Execution Contract | `evidence/extracts/undated_extracts_oc_012_strict_execution_contract_0027.md` |
| Model list | `evidence/extracts/undated_extracts_oc_013_model_list_0028.md` |
| Evidence archive samples | `evidence/extracts/undated_extracts_oc_010_evidence_archive_samples_0025.md` |

## Claim checklist

- OC-001: model count 16+ and rec_succ duplication supported by extracts
- OC-004: provider and version test shows failure
- OC-005: parameter config test shows invalid output
- OC-006: O3 contradicts itself in one response
- OC-007: Gemini uses plum = 2 in proof
- OC-009: DeepSeek uses Nat then rejects Nat
- OC-010: evidence archive exists with stated file classes
- OC-011: ten strategy failures documented
- OC-012: Strict Execution Contract is present
- OC-013: model list includes OpenAI, Google, DeepSeek
- OC-015: Gemini confession is quoted

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
