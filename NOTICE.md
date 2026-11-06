# Copyright and third-party notices

Copyright (c) 2026 The Yamabe3 contributors.

Original Lean source contributions to Yamabe3 are licensed under the
[Apache License, Version 2.0](LICENSE). The applicable upstream notices are
retained for adapted portions. [The source modification record](MODIFICATIONS.md)
identifies those portions, their upstream revisions, and the local changes.

## Adapted Lean sources

PoincareLib

Copyright (c) 2026 The PoincareLib contributors.

DifferentialGeometry

Copyright 2026 The DifferentialGeometry contributors

The Apache-2.0 text is included in [LICENSE](LICENSE). The unedited upstream
[PoincareConjecture notice](LICENSES/PoincareConjecture-NOTICE.txt) and
[DifferentialGeometry notice](LICENSES/DifferentialGeometry-NOTICE.txt) are
preserved with their original scope. The latter applies to the portions traced
to DifferentialGeometry in the source modification record.

## Lake dependencies

[Lake's lock file](lake-manifest.json) records the source URLs and commits.
These repositories are fetched separately by Lake.

| Dependencies | Upstream license |
| --- | --- |
| Mathlib, Batteries, Aesop, Qq, ProofWidgets, Plausible, LeanSearchClient, ImportGraph, Comparator, and lean4export | Apache-2.0 at the repository level. ImportGraph separately records MIT notices for its Graphology and Sigma.js assets. |
| Cli | MIT, Copyright (c) 2021 mhuisi. |
| PoincareConjecture and its PoincareLib | The pinned repository's notice identifies the contributions carrying Apache-2.0. The original PoincareLib distribution and the sources used here are identified in the [source modification record](MODIFICATIONS.md). |
