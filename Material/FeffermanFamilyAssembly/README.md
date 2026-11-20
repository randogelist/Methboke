# Periodic family growth and native assembly helpers

This is the second owned layer toward the [Fefferman D finite-family route](../../T3_NSE/D-Family-Obstruction/README.md).
Its proof candidates require matching external cached compilation and fresh
exact-type/axiom evidence before acceptance. No local Lean was executed.

| Source | Candidate scope |
|---|---|
| `GrowthSequence.lean` | Explicit diverging sequence from the temporal speed predicate; carrier membership and compact localization |
| `CopyBlowup.lean` | Translation, recentering, positive amplitude/spatial scaling, time compression and parabolic-copy blowup transport |
| `LocalDifferential.lean` | Locality of the actual native spatial and one-sided time derivatives, divergence, gradient, Laplacian, convection and forced equation |
| `DisjointNSE.lean` | Finite disjoint assembly preserves divergence and the nonlinear forced equation with exactly the sum of the prescribed forces |

The package has 22 helper theorems and one literal speed-predicate definition
check. Every name has an independent full consumer assertion and ordered
exact-type/axiom report in `Audit.lean`. The native one-sided `derivWithin`
convention is retained, including at the initial time.

The 72 preceding packages and 487 named audits remain intact. This package
brings the planned scope to 73 packages and 510 named reports plus the existing
QFB cutout. The projected compiled-module count is 420: the accepted 415 plus
four new sources and one endpoint wrapper. These are preparation counts,
not an observed compiler result.

The seed and its compatibility with the pinned Lean 4.33.0/Mathlib revision,
full PDE-preserving copy transformations, placement, force admission, energy,
periodization, same-force comparison, family existence and literal Fefferman-D
adapter remain separate obligations. Source-level assembly does not discharge
them. No compiler/dependency pin, workflow or previous proof/audit is modified.

`static-validation.json` records metadata/source coverage only. Its checks do
not execute Lean, Lake or a kernel and cannot establish theorem acceptance.
