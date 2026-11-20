# EHRENFEST-OBSTRUCTION

The project goal is the exact conditional theorem

```text
∀ ν > 0, StoppedCommutatorBound ν → ¬ NSE_B ν.
```

`StoppedCommutatorBound` is an explicit existential premise about one fixed
smooth datum and its actual canonical Fourier–Galerkin family. No witness of
that premise or unconditional NSE counterexample is asserted. The coefficient
predicate is defined directly; the full Hilbert-space commutator interpretation
remains a separate construction.

## Current evidence

**E09.bound and the exact conditional E10 theorem are A-tier accepted** at
`22431f032c868b8de1526767d7d32a2639f6a9ee`,
[run 44641040255](https://github.com/randogelist/Methboke/actions/runs/44641040255).
The [matching receipt](../../audits/material-22431f03-accepted/summary.json) records
411 modules (392 reused, 19 fresh), all 71 fresh package audits, all 448 named
audits plus QFB, 183 controls, publication and final acceptance. The theorem
audits use only `propext`, `Classical.choice` and `Quot.sound`. The 75 new scoped
declarations bring the accepted Ehrenfest total to 183. E07/E08 retain their
earlier acceptance; full E09 and the operator milestones remain open.

The accepted Ehrenfest portion is 30 owned sources, 16 packages and 183 named
declarations; its scalar-root source closure has 25 owned modules. The original
31-module design and nine logical blocks are historical counts.

## Internal proof chain

| Step | Exact role |
|---|---|
| INT01 | One fixed smooth datum and the canonical cutoff `N=n+1` |
| INT02 | Positive reciprocal, closed-slab continuity and exact signed drift |
| INT03 | Hypothetical global solution supplies a front with `T=1/γ<S=T+1` |
| INT04 | Cutoff-independent reference bounds and physical H1 tail |
| INT05 | Actual Fourier coefficient evolution and forced error equation |
| INT06 | Physical residual and signed error-energy estimates |
| INT07 | `D′ ≤ C(D+D³)+A/N²`, with zero initial error |
| INT08 | Interior exponential comparison derives eventual `D≤1` |
| INT09 | Smooth front implies eventual canonical enstrophy bound: E09.bound |
| INT10 | One large cutoff makes the literal `PreHit` guard hold |
| INT11 | Mean-value descent contradicts the positive terminal reciprocal |
| INT12 | Discharge hypothetical global smoothness and export E10 |

The actual reference bounds and error bootstrap are proved inside the chain;
no stability certificate or finite Fourier budget is added to the root. Root
imports only DynamicalRoot. Full H2 convergence and the operator construction
retain their original scopes in the ten-step checklist.

## Navigation

- [Cumulative mathematical derivation](../../EHRENFEST_OBSTRUCTION_B_TIER.txt)
- [Exact original ten-milestone checklist and root facets](CHECKLIST.md)
- [Implemented scalar proof route](FAST_ROUTE.md) and [current interfaces](FAST_INTERFACES.lean.txt)
- [Source-exact cutouts](../../LEAN_CUTOUTS/EhrenfestObstruction/README.md) and [identity reading order](../../LEAN_CUTOUTS/EhrenfestObstruction/FAST_IDENTITIES.md)
- [Implementation/evidence ledger](IMPLEMENTATION_STATUS.json), [obligations](obligations.json), [module design and actual mapping](MODULE_PLAN.json), [count reconciliation](COUNT_RECONCILIATION.json)
- [Original full layout](LEAN_LAYOUT.md), [operator/domain extension](OPERATOR_LAYOUT.txt), [original schematic interfaces](INTERFACES.lean.txt)
- [53 pinned source anchors](ANCHOR_INDEX_v0_3.json) and [readable index](ANCHOR_INDEX.md)

Weak_Fourierman_B, R0 and QFB are accepted foundations with unchanged statements
and evidence. In particular, WFB retains its finite-budget hypothesis. WFB is
not an extra hypothesis of the obstruction theorem.

Verification uses the unchanged compiler, dependencies, vendor and CI policies.
Only authorized external cached verification is permitted; no local Lean, Lake
or kernel execution is allowed. Failed attempts and earlier accepted evidence
remain recorded in the implementation ledger. No new verification run is
needed merely to rewrite this documentation around unchanged audited sources.

The [definition docstring](../../Material/MethbokeAddon/EhrenfestObstruction/Definitions.lean)
contains the physicists' reason trace: balance law, reciprocal observable,
formal normalized commutator, stopped quantifiers and the conditional
contradiction. The edited Lean text differs only in comments. Previous
proof acceptance remains pinned to `22431f`; fresh source validation of
this revision is pending under `CI_RUN_PLAN.json`.
