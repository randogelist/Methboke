# FDSNR3Main

Canonical whole-space FDSN_R3 root construction from the original Seed to the full Family contract, with one concrete physical velocity/force family and all sixteen endpoint obligations assembled.

Status: **A-tier accepted at `572fd9ee`**.

This package registers **1 named declaration** in the full verification
scope of **548 modules, 137 fresh package audits and 1,320 named type/axiom
reports**. Exact source: [`572fd9ee`](https://github.com/randogelist/Methboke/tree/572fd9ee69a6b641f435cbfb2ef74e034809c583/Material/FDSNR3Main);
[external run 44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720);
[retained evidence](../../audits/fdsn-r3-572fd9ee-accepted/summary.json).
Acceptance belongs to that tested source and audit identity; later
documentation edits do not change the tested revision.

The package imports the actual owned source through Endpoint.lean. Audit.lean contains independent explicit consumer statements, literal definition contracts where applicable, and complete named type/axiom reports. No local Lean execution or local kernel audit is part of preparation.

Project scope: whole-space FDSN_R3. The canonical theorem
`MethbokeAddon.FDSNR3.FDSN_R3` has the original type
`Seed ν T u p F → Family ν T u p F`. The root audit checks both that exact
type and an independent expansion of the full common-witness contract.
The conclusion includes all five Family clauses, common compact temporal
support, exact initial and terminal-tail agreement, and equal energy and
dissipation histories. The integrated-dissipation and fixed-frame helical
coefficient identities are separately audited in the realization and
helical-frame packages. Seed existence is not asserted, and the force varies
with the family parameter. Existing pins and earlier accepted evidence remain unchanged.
