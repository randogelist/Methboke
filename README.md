# Methboke

The project goal is the exact conditional **EHRENFEST_OBSTRUCTION** theorem
for unforced periodic three-dimensional Navier--Stokes:

```text
ν > 0 → StoppedCommutatorBound ν → ¬ NSE_B ν.
```

`NSE_B ν` is the actual universal global smooth-solution statement for smooth,
divergence-free, mean-zero data on the unit three-torus. The stopped bound is
one explicit hypothesis on the canonical Galerkin family of a fixed smooth
datum. **Its witness remains unproved.** No global custom axiom is added.
The working branch is `main`.

## Current evidence

[Run 44641040255](https://github.com/randogelist/Methboke/actions/runs/44641040255)
at `22431f032c868b8de1526767d7d32a2639f6a9ee` has completed successfully.
**The exact conditional root and E09.bound are A-tier accepted.** The run passed
**411 modules** (392 reused, 19 fresh), **71 fresh endpoint packages**, **448
unique named type/axiom audits plus QFB**, and **183 external controls**.
Required publication and final acceptance passed. All theorem axioms are limited
to `propext`, `Classical.choice` and `Quot.sound`.

The [matching evidence](audits/material-22431f03-accepted/summary.json),
[independent review](audits/material-22431f03-accepted/independent-review.json)
and [complete archive](audits/material-22431f03-accepted/evidence.zip) retain
the exact source, types, audit origins and hashes. Independent review passed
1,488 consistency checks. The [A-tier register](EHRENFEST_OBSTRUCTION_A_TIER.txt)
states the accepted theorem and its explicit premise.

The run adds 75 accepted declarations to the prior 108, giving **183 accepted
Ehrenfest declarations**. E07/E08 acceptance at `7908890a` remains preserved.
The failed `d6e74ba8` attempt is retained as history; `22431f` repairs its single
continuity proof without changing statements, audits or dependency pins.

## Conditional proof and its scope

The [StoppedCommutatorBound docstring](Material/MethbokeAddon/EhrenfestObstruction/Definitions.lean)
now explains the physics motivation: enstrophy production, a bounded
reciprocal observable, the Heisenberg/Koopman commutator and stopped uniform
descent. It separates that interpretation from the unproved witness and
full operator realization. This comment-only Lean revision preserves all
declarations; its fresh external source validation is pending.

Assume the stopped bound and a global smooth solution for its fixed datum.
Smooth-front Galerkin stability gives an eventual uniform enstrophy bound on
`[0,1/γ]`. Choose one sufficiently large cutoff whose threshold exceeds that
bound. Its reciprocal observable then has derivative at most `-γ` throughout
the slab interior. Mean-value comparison forces its terminal value to be
nonpositive, contradicting its strict positivity.

The root uses the actual H1 error estimate and eventual bound **E09.bound**.
It does not require the stronger full E09 H2-convergence theorem or the full
Hilbert-space operator realization. Those retain their separate original
checklist scopes. The accepted conditional root does not construct a singular witness or
complete all ten operator-program milestones.

| Item | Exact scope and status |
|---|---|
| E07 stopped scalar hitting | Accepted, with exact external evidence |
| E08 cutoff-uniform threshold escape | Accepted under the explicit stopped premise |
| E09.bound actual-front eventual enstrophy bound | A-tier accepted at `22431f`; scoped helper |
| E10 `EHRENFEST_OBSTRUCTION` | A-tier accepted at `22431f`; explicit stopped premise |
| Stopped-bound witness | Open |
| Full operator/domain/core realization | Open |
| Full E09 `C([0,T];H2)` convergence | Open |

## Accepted foundations

**Weak_Fourierman_B remains accepted in its original finite-budget scope.**
[Run 44566880192](https://github.com/randogelist/Methboke/actions/runs/44566880192)
at `fdb515d8` passed 365 modules, 55 fresh packages, 265 declaration audits plus
QFB and 183 controls. Its full finite squared Fourier budget up to
`min(Tmax,τ_Q)` implies global smooth continuation of the same velocity and
normalized pressure, where `τ_Q=||a||₂⁴/(8π²ν⁵)`. The budget remains a hypothesis.
Its accepted local-existence, uniqueness and physical-estimate sources remain
available; no extra WFB budget premise is inserted into the obstruction root.

Accepted R0 supplies finite-cap admission with its actual cap premise. The
original QFB result preserves eventual-tail, energy and post-cutoff uniqueness
semantics. Universal Fourier-budget finiteness and universal analytic-germ
extension R1 remain open and outside the current goal.

The [WFB evidence archive](audits/material-fdb515d8/accepted-evidence.zip),
[WFB preprint](PAPER_PREPRINT_PDF/WFB/WFB_FOURIER_BUDGET_PREPRINT.pdf) and
[LaTeX source](PAPER_PREPRINT_PDF/WFB/WFB_FOURIER_BUDGET_PREPRINT.tex) remain intact.

## Repository map

| Path | Purpose |
|---|---|
| [GPT.txt](GPT.txt) | Current goal, precise premise, constructive chain and operating context |
| [INDEX-WORTHY.txt](INDEX-WORTHY.txt) | Current substantiated results with exact scope and evidence |
| [SOURCE_STATUS.json](SOURCE_STATUS.json) | Named goal, root/foundation status and source identities |
| [Cumulative derivation](EHRENFEST_OBSTRUCTION_B_TIER.txt) | Complete conditional mathematical chain |
| [Ehrenfest package](PREPRINT_FORMALISATION/EhrenfestObstruction/README.md) | Root plan, original ten-milestone checklist and evidence ledgers |
| [Implementation ledger](PREPRINT_FORMALISATION/EhrenfestObstruction/IMPLEMENTATION_STATUS.json) | Accepted, pending and historical attempts |
| [Source cutouts](LEAN_CUTOUTS/EhrenfestObstruction/README.md) | Exact source identities and preserved proof context |
| [Root source](Material/MethbokeAddon/EhrenfestObstruction/Root.lean) | Literal conditional endpoint |
| [Material](Material/README.md) | Native sources, endpoint packages and complete audits |
| [Historical registers](audits/goal-transition-22431f/README-registers.md) | Byte-identical pre-transition documents and their provenance |

## Verification

Lean execution is external and cached only. Local Lean, Lake invoking Lean and
local kernel audits are forbidden. The pin is `leanprover/lean4:v4.33.0` with
Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`; the dependency lock, vendor
sources and acceptance policy remain unchanged.

The existing [Material workflow](.github/workflows/material.yml) restores
compatible accepted objects, compiles affected owned modules and reruns every
required exact-type/theorem-axiom audit. Publication follows complete accepted
verification. A missing official Mathlib object cache is an obstruction, not
permission to rebuild Mathlib from source. Standard theorem axioms are limited
to `propext`, `Classical.choice` and `Quot.sound`.

The user-selected goal migration changes documentation authority, not theorem
statements or historical evidence. Superseded priorities and status narratives
are preserved in the historical register archive instead of remaining as
conflicting current instructions.
