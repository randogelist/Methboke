# Quasi-Fefferman B

The accepted root is
`QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED : QuasiFeffermanBStatement`.
Its original contract supplies Leray–Hopf existence and eventual smooth tails,
tail energy equality, and uniqueness from post-cutoff traces. It does not
assert smoothness before the cutoff or full Fefferman-B global regularity.

| Material | Canonical location |
|---|---|
| Original native Lean root | [Endpoints/Root.lean](../../../Material/_vendor/QuasiFeffermanB/Endpoints/Root.lean) |
| Endpoint package and audit | [QFBRoot](../../../Material/QFBRoot/README.md) |
| Complete standalone root cutout | [Cutouts.lean](../../../LEAN_CUTOUTS/Cutouts.lean) |
| Cutout provenance | [provenance.json](../../../LEAN_CUTOUTS/provenance.json) |
| Latest retained complete verification | [3335bbc5 receipt](../../../audits/material-3335bbc5-comments/summary.json) |

The cutout and native sources keep their established paths because they are
shared audited build inputs. This folder provides their periodic-domain entry
point. The vendor source is pinned to Methlib
`96033dd69c994bec337a87369a6c27256e724980`; the shared runner freshly checks
the QFB cutout alongside the registered endpoint packages.

See [WFB](../WFB/README.md) for the finite-budget continuation program and
[GPT.txt](../../../GPT.txt) for current project context and scope boundaries.

[Source index](SOURCE_INDEX.json) lists the canonical Lean files and endpoint packages.
