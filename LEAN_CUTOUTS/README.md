# Native QFB root cutout

`Cutouts.lean` contains the original QFB root interface and its complete proof
body, followed by a fresh type check and theorem-level axiom audit. The upstream
root source is preserved verbatim. Its declaration remains
`QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED : QuasiFeffermanBStatement`.

The selected interface is aggregated into one file. Its dependencies remain
native Lean modules under `Material/_vendor`; they are not flattened into this
file. Retaining module boundaries preserves private declarations, notation and
module initialization semantics. The complete QFB root closure comprises 256
local source modules. The complete Material collection contains 269 local source
modules: 74 QFB and 195 SingularClosure modules. It requires no build-time Methlib
checkout. Mathlib and its dependencies remain pinned by the Material lockfile.

`provenance.json` records the original repository, commit, source, theorem,
source hashes and dependency manifest. The source is Methlib commit
`96033dd69c994bec337a87369a6c27256e724980`; Lean is pinned to `4.33.0` and Mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`.

After restoring compatible objects and building the Material dependencies, an
authorized external runner checks the standalone file from the `Material`
directory:

```sh
lake env lean ../LEAN_CUTOUTS/Cutouts.lean
```

The file imports the original root's prerequisites, not the original root module,
so its proof is elaborated again without redefining an imported declaration.
The audit accepts only `propext`, `Classical.choice` and `Quot.sound`.

The [inherited upstream QFB run](https://github.com/randogelist/Methlib/actions/runs/43801307847)
records the original endpoint. Matching validation of this single-file packaging
passed in [Methboke run 44052579373](https://github.com/randogelist/Methboke/actions/runs/44052579373)
at source `6440270ffe9b05b2956cd34c59c65f2fe341e8b8`. The proof was elaborated
and its exact type and axioms checked freshly in 3.767s. The axiom list is
`[Classical.choice, Quot.sound, propext]`.

The [accepted report](../audits/material-6440270/current.json) records cutout
SHA-256 `b67344ddb9e509d7224b529bcd1022181360b973a17602aca8a66d4cdc273f7b`
and audit-log SHA-256 `256ff6ec53da11d10e85943715481629444de75f37794a5ecb86015ea42c581d`.
This acceptance identifies the tested source, compiler and dependency pins;
each later verification must rerun its own audit. No local Lean execution was
performed.

QFB asserts Leray–Hopf existence and regular, energy-equality, unique futures
after its cutoff. It does not establish universal extension of a local analytic
germ to the cap, or full Fefferman B. Those obligations remain explicit in the
project records.
