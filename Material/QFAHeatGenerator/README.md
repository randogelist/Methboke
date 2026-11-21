# Actual heat generator and the equation from the initial trace

This package constructs the strong `SpatialL2` time derivative of the actual
heat velocity for every positive viscosity, arbitrary physical H1 datum and
positive time. The derivative is exactly the viscosity times the physical
Laplacian of the already constructed H2 trajectory.

The same derivative belongs to `MemLp 2` on every finite nonnegative time
window and is Bochner integrable down to zero. The true continuous heat path
retains its original L2 initial trace and satisfies the integrated heat
equation. Exact derivative energy is viscosity divided by two times the
drop in actual H1 enstrophy.

Nine public theorems are checked by eleven independent consumers. They
include expanded weak-gradient enstrophy, one common path carrying the
derivative and integral claims, and the exact coefficient for ordinary
positive real viscosity. Every theorem has a named type and transitive
axiom audit, permitting only `propext`, `Classical.choice` and `Quot.sound`.

Matching cached external acceptance passed at `809aadc6`, [run 44853804320](https://github.com/randogelist/Methboke/actions/runs/44853804320).
All nine theorems and eleven consumers passed in the complete 528-module,
106-package, 1,411-report run, with fresh QFB, complete publication and the final gate.
[Exact independent review](../../audits/material-809aadc6-qfa-heat-generator-accepted/independent-review.json) and
[new theorem index](../../audits/material-809aadc6-qfa-heat-generator-accepted/new-declaration-index.json).

The statements assume no
supplied derivative, time-integrability or regularity witness. The H2
trajectory's value at zero is used only inside integrals; no H2 initial
trace or H1-valued time derivative is asserted. Forced heat, its maximal
regularity estimate and nonlinear local existence are subsequent layers.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatGenerator.lean) ·
[Independent consumers](Audit.lean) ·
[Derivation](../../R3_NSE/QFA/DERIVATIONS/HEAT_GENERATOR_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
