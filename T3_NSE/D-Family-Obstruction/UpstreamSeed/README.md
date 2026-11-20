# Direct Fefferman D endpoint

Project goal: **Fefferman D**. This isolated project prepares
`Methboke.FeffermanD.Fefferman_D` by applying
`NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic` from
[openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd).
This is explicit reuse of the upstream proof, not a new singular-seed mechanism.
**Status: candidate, pending matching external verification.**

For every viscosity `ν>0`, the endpoint states that there are smooth periodic
initial data and a smooth periodic force satisfying all-order time-decay bounds,
for which there is no global smooth periodic velocity and pressure solution.
The global competitor has no added energy, mean-zero or pressure-gauge condition.
The independent [audit](Audit.lean) expands these contracts literally, including
the right time derivative at zero and periodic pressure, and separately checks
the full type of the imported theorem and [local endpoint](Endpoint.lean).

The source closure has604 upstream modules. It uses Lean4.34.0-rc2 and
Mathlib85e3a25e006c35636f0e53b0e9296caca2685bc0. The unchanged `Material/`
project retains its own Lean4.33.0 and accepted audit scope. There are no cross-pin
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

The stronger prescribed-site `Fefferman_D_Family_obstruction` is separate and
remains open. Acceptance of this direct endpoint will not certify that family.
