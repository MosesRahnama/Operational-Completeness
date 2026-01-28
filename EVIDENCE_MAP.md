# Evidence Map

This file explains how to locate evidence in this repo after the file rename pass.

## Scope and source policy

This repo is standalone. The KO7 repo is referenced only.
Lean code is used only when needed, and only from:
`C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKO7\OperatorKO7_Complete_Documentation.md`

Legacy sources hold older code that hit a wall. Files named `termination.md` or `fails` are high value failure evidence.
HTML exports are excluded in favor of the original MD or PDF sources.

## How to find a file

Use `evidence/INDEX.csv` to map any prior source path to the new repo path.
Each row includes `source_path` and `dest_rel` so you can locate the file.

## Key folders

- `evidence/maps` holds claim lists, claim maps, and coverage tables.
- `evidence/docket` holds failure docket and method notes.
- `evidence/extracts` holds short extracts used in the paper.
- `evidence/tests` holds model test artifacts.
- `evidence/lean_graveyard` holds failed proof attempts.
- `evidence/analysis` holds diagnostics and autopsies.

## Index files

- `evidence/INDEX.csv` contains full source to dest mapping, hashes, size, and file time.
- `evidence/INDEX.md` contains counts by category.

## Claim map quick links

Primary claim map:
- `evidence/maps/undated_maps_02_claim_map_0007.md`

Key evidence extracts:
- OC-001 model count 16+: `evidence/extracts/undated_extracts_oc_001_model_count_16plus_0017.md`
- OC-001 rec_succ duplication: `evidence/extracts/undated_extracts_oc_001_rec_succ_duplication_0018.md`
- OC-004 provider and version test: `evidence/extracts/undated_extracts_oc_004_provider_version_0019.md`
- OC-005 parameter config test: `evidence/extracts/undated_extracts_oc_005_param_config_0020.md`
- OC-006 O3 contradiction: `evidence/extracts/undated_extracts_oc_006_o3_contradiction_0021.md`
- OC-007 Gemini plum = 2: `evidence/extracts/undated_extracts_oc_007_gemini_plum2_0022.md`
- OC-009 DeepSeek contradiction: `evidence/extracts/undated_extracts_oc_009_deepseek_contradiction_0024.md`
- OC-010 evidence archive samples: `evidence/extracts/undated_extracts_oc_010_evidence_archive_samples_0025.md`
- OC-011 strategy failures: `evidence/extracts/undated_extracts_oc_011_strategy_failures_0026.md`
- OC-012 Strict Execution Contract: `evidence/extracts/undated_extracts_oc_012_strict_execution_contract_0027.md`
- OC-013 model list: `evidence/extracts/undated_extracts_oc_013_model_list_0028.md`
- OC-015 Gemini confession: `evidence/extracts/undated_extracts_oc_015_gemini_confession_0030.md`
