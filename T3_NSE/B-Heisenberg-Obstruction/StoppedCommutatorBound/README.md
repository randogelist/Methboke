# StoppedCommutatorBound

The accepted conditional root is

```text
∀ ν > 0, StoppedCommutatorBound ν → ¬ NSE_B ν.
```

For one fixed smooth datum, the hypothesis requires a uniform negative drift
of the bounded reciprocal enstrophy observable before a growing threshold is
reached. A hypothetical global smooth solution would supply an eventual
Galerkin enstrophy bound; the resulting uninterrupted descent contradicts
positivity of that observable.

| Material | Location |
|---|---|
| Cumulative derivation | [EHRENFEST_OBSTRUCTION_B_TIER.txt](EHRENFEST_OBSTRUCTION_B_TIER.txt) |
| Accepted theorem register | [EHRENFEST_OBSTRUCTION_A_TIER.txt](EHRENFEST_OBSTRUCTION_A_TIER.txt) |
| Historical amendment proposal | [Interior amendments](EHRENFEST_OBSTRUCTION_INTERIOR_AMENDMENTS_B_TIER.txt) |
| Checklist, interfaces and implementation ledger | [PREPRINT_FORMALISATION](PREPRINT_FORMALISATION/README.md) |
| Indexed identities and source snapshots | [LEAN_CUTOUTS](LEAN_CUTOUTS/README.md) |
| Literal definition and physicists' reason trace | [Definitions.lean](../../../Material/MethbokeAddon/EhrenfestObstruction/Definitions.lean#L73) |
| Canonical Lean root | [Root.lean](../../../Material/MethbokeAddon/EhrenfestObstruction/Root.lean) |
| Latest retained complete verification | [3335bbc5 receipt](../../../audits/material-3335bbc5-comments/summary.json) |

The accepted implication uses only the standard Lean axioms. Existence of a
stopped-bound witness remains open, as do the full Hilbert-space operator
realization and the stronger full E09 H2-convergence milestone. The physical
interpretation does not supply those missing results.

Canonical Lean sources remain in the shared `Material` workspace.
[GPT.txt](../../../GPT.txt) is the current project context; the organization
branch changes locations and navigation without adopting a new mathematical goal.

[Source index](SOURCE_INDEX.json) lists the canonical Lean files and endpoint packages.
