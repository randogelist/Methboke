# Direct Fefferman D endpoint

Project goal: **Fefferman D**. This isolated project proves
`Methboke.FeffermanD.Fefferman_D` by applying
`NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic` from
[openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd).
This is explicit reuse of the upstream proof, not a new singular-seed mechanism.
**Status: A-tier accepted by matching external verification.**

The tested revision is `66a529248d3198ed70dc5489d82868bc33a37796`.
[Run 44768857811](https://github.com/randogelist/Methboke/actions/runs/44768857811)
passed 605 modules, literal contract/type checks and five fresh named axiom
reports (three predicates and two theorems), with only
`propext`, `Classical.choice` and `Quot.sound` and no `sorryAx`.
Evidence retention, cache publication and final acceptance passed. The
[acceptance receipt](ACCEPTANCE.json) identifies the retained
[artifact 14649221097](https://github.com/randogelist/Methboke/actions/runs/44768857811/artifacts/14649221097),
whose SHA256 is `f01b81cc50619bf79e45eb8620f0ef29ef0927f1808a153f40854194e666727b`.

For every viscosity `ν>0`, the endpoint states that there are smooth periodic
initial data and a smooth periodic force satisfying all-order time-decay bounds,
for which there is no global smooth periodic velocity and pressure solution.
The global competitor has no added energy, mean-zero or pressure-gauge condition.
The independent [audit](Audit.lean) expands these contracts literally, including
the right time derivative at zero and periodic pressure, and separately checks
the full type of the imported theorem and [local endpoint](Endpoint.lean).

The accepted closure contains 605 modules. It uses Lean `4.34.0-rc2` and
Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The unchanged `Material/`
project retains its own Lean `4.33.0` and accepted audit scope. There are no cross-pin
imports. Exact compiler, dependency, source, object and audit identities are
recorded by the isolated external workflow. Official dependency objects must be
available; missing ones do not authorize a Mathlib source build. A first own
closure cache miss is recorded and its source modules are compiled externally.
All endpoint audits run freshly, and passed objects are published only after
complete verification. No local Lean, Lake or kernel execution is permitted.

[CI_RUN_PLAN.json](CI_RUN_PLAN.json) records the intended pins and scope.
[Provenance](provenance/source-identity.json) identifies the inspected source;
[LICENSE](provenance/LICENSE) preserves its Apache-2.0 license. The upstream
challenge files containing intentional statement placeholders are not imported.

The earlier run `44663007873` at
`dd0e3550f7c662e3251d48194f4f70f3f6d9f628` passed compilation and audits but
failed evidence retention. The hidden-directory upload repair and accepted
rerun resolved that evidence obstruction; the earlier run remains history.

The stronger prescribed-site `Fefferman_D_Family_obstruction` is separate.
Its [cumulative B-tier derivation](../Fefferman_D_Family_obstruction_B_TIER.txt)
uses the stronger compact whole-space seed, per-copy quarter-cube periodization,
torus translations and same-force comparison. It includes localized small-budget
families and the zero-force obstruction. The family and these refinements
remain open at A-tier; acceptance of the direct endpoint does not certify them.
