# Evidence Archive

This folder contains curated files and raw source files used by the paper.

## Scope and sources

This repo is standalone. The KO7 repo is referenced only.
Lean code is used only when needed, and only from:
`C:\Users\Moses\math_ops\OperatorKernelO6\OperatorKO7\OperatorKO7_Complete_Documentation.md`

Legacy sources hold older code that hit a wall. Files named `termination.md` or `fails` are high value failure evidence.
HTML exports are excluded in favor of the original MD or PDF sources.

## Structure

```
evidence/
  maps/
  docket/
  extracts/
  tests/
  lean_graveyard/
  analysis/
  INDEX.md
  INDEX.csv
```

Each file name follows this pattern:

YYYY-MM-DD_category_slug_NNNN.ext

For each entry, INDEX.csv records the source path, size, sha256, and file time.
Use `extracts/` for short, citable passages when full transcripts are not needed.
