# Evidence Map

This file explains how to locate evidence in this repo after the file rename pass.

## Scope and source policy

This repo is standalone. The KO7 repo is referenced only.
Lean code is used only when needed, and only from:
`C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKO7\OperatorKO7_Complete_Documentation.md`

Legacy folders hold older code that hit a wall. Files named `termination.md` or `fails` are high value failure evidence.

## How to find a file

Use `evidence/INDEX.csv` to map any prior source path to the new repo path.
Each row includes `source_path` and `dest_rel` so you can locate the file.

## Key folders

- `evidence/maps` holds claim lists, claim maps, and coverage tables.
- `evidence/docket` holds failure docket and method notes.
- `evidence/extracts` holds short extracts used in the paper.
- `evidence/tests` holds model test artifacts.
- `evidence/transcripts` holds raw chat logs.
- `evidence/lean_graveyard` holds failed proof attempts.
- `evidence/analysis` holds diagnostics and autopsies.
- `evidence/archive` holds legacy or uncategorized files.

## Index files

- `evidence/INDEX.csv` contains full source to dest mapping, hashes, size, and file time.
- `evidence/INDEX.md` contains counts by category.
