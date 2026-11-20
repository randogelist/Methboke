# Pinned source closure

`repository = randogelist/Methlib`

`commit = 96033dd69c994bec337a87369a6c27256e724980`

`Lean = 4.33.0`

`Mathlib = db584cd6d46c92f209a44c0f1c829460d327499d`

| Component | Module count |
|---|---:|
| QuasiFeffermanB | 74 |
| SingularClosure | 195 |
| Total | 269 |

Source policy: exact upstream UTF-8 bytes, including existing notices. All 269 Git blob hashes match the pinned source. The original 256-module QFB closure is extended by the 13 modules required for the small-data combined endpoint. Local imports form a closed dependency graph; external imports belong to Mathlib.

`source-manifest.json` records module names, local paths relative to `Material`, immutable upstream paths and revision, Git blob hashes, SHA-256 hashes, byte counts and direct imports. Import and forbidden-token scans exclude comments and string literals.

`provenance/` retains the exact upstream toolchain, QFB package configuration, foundation package configuration and dependency lock. The build package may relocate these modules without changing module names or proof bodies.

No upstream root `LICENSE` file was present at the pinned revision. No replacement license is asserted. Per-file notices remain unchanged.

`local Lean executions = 0`.

`source extraction != new compiler pass`.
