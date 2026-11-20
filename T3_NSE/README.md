# Periodic three-dimensional Navier–Stokes

This folder organizes the project on the unit three-torus `T³ = R³/Z³`.
The layout was validated on `codex/reorganize-nse-domains` for integration into
`main`; the mathematical goal and every accepted theorem premise are preserved.

| Program | Entry point |
|---|---|
| D forced family obstruction — current goal | [Fefferman D route](D-Family-Obstruction/README.md) |
| B regularity classes | [WFB](B-Regularity-class/WFB/README.md) and [QFB](B-Regularity-class/QFB/README.md) |
| B Heisenberg obstruction | [StoppedCommutatorBound](B-Heisenberg-Obstruction/StoppedCommutatorBound/README.md) |

The current user-selected goal is Fefferman D. The
[direct literal endpoint](D-Family-Obstruction/UpstreamSeed/README.md) is
**accepted at A-tier** at `66a529248d3198ed70dc5489d82868bc33a37796` by
[run 44768857811](https://github.com/randogelist/Methboke/actions/runs/44768857811):
605 modules, literal contract/type checks and five fresh named axiom reports
(three predicates and two theorems), standard axioms only, with retained evidence
and final acceptance. It explicitly reuses the
upstream proof in the isolated Lean `4.34.0-rc2` project.

The stronger local target remains the finite prescribed-site family. Its native
foundations and assembly helpers are accepted:
**50 helper theorems and 12 contract/predicate declarations**. The first layer
was accepted at 77a64245; the second at f19531bc. See the
[foundation register](D-Family-Obstruction/FEFFERMAN_D_FOUNDATION_A_TIER.txt) and
[assembly register](D-Family-Obstruction/FEFFERMAN_D_ASSEMBLY_A_TIER.txt).
The family is closed at B-tier from the pinned compact seed, while its full
A-tier formalization remains open.

The [cumulative version 1.6 derivation](D-Family-Obstruction/Fefferman_D_Family_obstruction_B_TIER.txt)
uses per-copy quarter-cube periodization, torus translations, disjoint assembly
and same-force comparison; no generic-radius wrapper is needed. It also places
supports in prescribed neighborhoods and an arbitrarily short window around
time one, makes energy/dissipation/force norms arbitrarily small, and meets
finite mixed-norm force budgets with `3/p + 2/q > 3`. Identically zero forcing
is incompatible with its zero-data blowup; these localized witnesses also
require nonzero projected force on every terminal interval. No unforced
counterexample or novelty claim follows. Close literature precedents are
recorded in the derivation and [route index](D-Family-Obstruction/FEFFERMAN_C_D_FAMILY_OBSTRUCTION_INDEX.txt).

Native 4.33 acceptance covers growth extraction, geometric parabolic
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
