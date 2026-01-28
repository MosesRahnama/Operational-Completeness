# Evidence Crosswalk

The file rename pass keeps every source path in `evidence/INDEX.csv`.
Use it as a lookup table from `source_path` to `dest_rel`.

Example use case:
1. Search for the source path you know.
2. Read the `dest_rel` column to locate the file in the repo.

No files are deleted. Old top level evidence files are stored in `evidence/_legacy`.

Notes:
- This repo is standalone. The KO7 repo is referenced only.
- Legacy folders hold older code that hit a wall.
- Files named `termination.md` or `fails` are high value failure evidence.
