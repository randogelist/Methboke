# Periodic three-dimensional Navier–Stokes

This folder organizes the project on the unit three-torus `T³ = R³/Z³`.
The layout was validated on `codex/reorganize-nse-domains` for integration into
`main`; the mathematical goal and every accepted theorem premise are preserved.

| Program | Entry point |
|---|---|
| D forced family obstruction — current goal | [Fefferman D route](D-Family-Obstruction/README.md) |
| B regularity classes | [WFB](B-Regularity-class/WFB/README.md) and [QFB](B-Regularity-class/QFB/README.md) |
| B Heisenberg obstruction | [StoppedCommutatorBound](B-Heisenberg-Obstruction/StoppedCommutatorBound/README.md) |

The current user-selected goal is Fefferman D, using the finite prescribed-site
family route. Its native foundations and assembly helpers are accepted:
**50 helper theorems and 12 contract/predicate declarations**. The first layer
was accepted at 77a64245; the second at f19531bc. See the
[foundation register](D-Family-Obstruction/FEFFERMAN_D_FOUNDATION_A_TIER.txt) and
[assembly register](D-Family-Obstruction/FEFFERMAN_D_ASSEMBLY_A_TIER.txt).
The full family witness remains unproved.

A direct literal D endpoint is also prepared in
[UpstreamSeed](D-Family-Obstruction/UpstreamSeed/README.md), using explicit
upstream proof reuse and isolated external 4.34 verification, which remains
pending. Native 4.33 acceptance covers growth extraction, geometric parabolic
blowup transport, operator locality including time zero, and conditional finite
disjoint NSE assembly. It does not supply seed admission, transformed-copy PDE,
packing, energy, force admission, periodization or same-force comparison.

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
