# Periodic three-dimensional Navier–Stokes

This folder organizes the project on the unit three-torus `T³ = R³/Z³`.
The layout was validated on `codex/reorganize-nse-domains` for integration into
`main`; the mathematical goal and every accepted theorem premise are preserved.

| Program | Entry point |
|---|---|
| B regularity classes | [WFB](B-Regularity-class/WFB/README.md) and [QFB](B-Regularity-class/QFB/README.md) |
| B Heisenberg obstruction | [StoppedCommutatorBound](B-Heisenberg-Obstruction/StoppedCommutatorBound/README.md) |

The program folders contain their derivations, registers, plans and publication
material. [Material](../Material/README.md) remains the shared verified Lean
workspace, with its existing namespaces, imports, dependency pins and audits.
The [evidence archive](../audits) retains the exact tested revisions.

[GPT.txt](../GPT.txt) is the current project context; [SOURCE_STATUS.json](../SOURCE_STATUS.json)
records verification status. [R3_NSE](../R3_NSE/README.md) separately reserves
the whole-space domain. These folder names introduce no new Lean namespaces
or mathematical assumptions.

See the [formalisation index](FORMALISATION_INDEX.md) and
[publication index](PUBLICATION_INDEX.md) for the relocated research collections.
