# Whole-space stopped-commutator obstruction

The selected target is the R3 analogue of the accepted periodic conditional
obstruction: for every positive viscosity, StoppedCommutatorBoundR3 implies
the negation of the literal NSE_A statement.

**The native root remains open.** This branch implements concrete foundation
layers from the assented sixteen-step plan. Exact source, audit and external
run status are recorded in [IMPLEMENTATION_STATUS.json](IMPLEMENTATION_STATUS.json).

The [cumulative B-tier TXT](NSE_A_EHRENFEST_B_TIER.txt) contains the analytical
architecture and named literature inputs. The [Lean reuse index](NSE_A_EHRENFEST_LEAN_REUSE_INDEX_v0_2.txt)
records 56 source cards and 175 declaration names, with pinned source
identities and precise limitations.

## Current construction

| Layer | Native module | Scope |
|---|---|---|
| I01 contract | Contracts | Literal Schwartz data, actual smooth unforced equation, uniform finite energy, unrestricted pressure gauge; zero witness |
| I02 cutoff | SharpCutoff | Actual closed-ball Fourier cutoff at n+1, contraction, projection, self-adjointness, Leray commutation, native H1 transport |
| I03 carrier | Carrier | Closed complete fixed-point space for cutoff and Leray projection |
| I02 approximation | Approximation | Actual L2/H1 strong convergence and compact-trajectory uniform convergence |
| I03 inverse representation | FourierL1L2 | Actual inverse integral agrees a.e. with the native L2 inverse; polynomial-moment smoothness |
| I03 smooth representative | SmoothRepresentative | Constructed bounded smooth representative with finite nonsharp fixed-cutoff norm bound |
| I03 derivatives | Bandlimited | New real weak derivative witnesses and physical H2 admission; exact delivered scope in the endpoint manifest |

All modules are under Material/MethbokeAddon/R3Ehrenfest/. New statements
remain candidates until matching external compilation and complete exact
type/axiom audits pass. A foundation-stage success does not establish the root.

## Remaining mathematical work

Construct the regularized family from the actual nonlinear whole-space
equation, with uniqueness, energy cancellation, global continuation and
actual reciprocal-enstrophy drift. Prove the full H1 error estimate with
whole-space Sobolev bounds and a cutoff-independent constant.

Derive closed-slab C_t H2 admission and the projected equation for the same
smooth finite-energy solution in NSE_A. Adding this conclusion as a
solution-contract field would change the target. Existence of a stopped-bound
witness remains a separate question after the conditional implication.

## Verification

The branch codex/nse-a-r3-ehrenfest starts from main at
5f53d3eb320cc3860a9f28384a825349e0df5e21. It retains the existing Material
Lean 4.33.0 compiler, locked dependencies and canonical cache policy.
Each new endpoint has an independent exact-type consumer and named axiom
report. Only authorized cached external CI executes Lean.

## First external attempt

[Run 44872662109](https://github.com/randogelist/Methboke/actions/runs/44872662109)
rejected the first candidate on two Lean Fourier-map rewrite mismatches.
The repaired statements are unchanged. No new audited scope was accepted in
that attempt; its [receipt](../../../../audits/r3-ehrenfest-ba451454-failed/summary.json)
is retained. The source-count check passed at the exact attempted commit.

The next prepared batch has seven packages and 111 named declarations. Its
latest immutable source snapshot is 80f36647edc71bc36f94cae410d958b5157be862;
this is source preparation, with external acceptance still pending.

## Second external attempt

[Run 44873417429](https://github.com/randogelist/Methboke/actions/runs/44873417429)
compiled Contracts, SharpCutoff and Carrier, then rejected later elaboration
failures. The [exact failed receipt](../../../../audits/r3-ehrenfest-aa0fd8ee-failed/summary.json)
is retained. The third candidate repairs explicit types and namespace resolution
with all 111 declaration statements unchanged. No new audited scope is accepted
until the full gate and the scoped R3 audit pass.

## External attempt 3

[Run 44874347518](https://github.com/randogelist/Methboke/actions/runs/44874347518) failed before full acceptance.
Five new source modules compiled, including Bandlimited and FourierL1L2. Approximation retained one scalar zero-power simplification error. SmoothRepresentative was reached and reported notation, measurable-ball inference, Fourier-map specialization and function-composition errors.
Explicit scalar-zero simplification, unambiguous ENNReal/top notation, typed measurable ball, real-linear Fourier-map specialization and explicit function composition. The seven-package/111-declaration scope and theorem statements are preserved.
The [exact receipt](../../../../audits/r3-ehrenfest-66461374-failed/summary.json) is retained.
All seven packages remain candidates pending matching full and scoped audits.

## External attempt 4

[Run 44874923670](https://github.com/randogelist/Methboke/actions/runs/44874923670) failed before full acceptance.
Six new source modules and their endpoints compiled, including SmoothRepresentative. Approximation had one remaining diagnostic: an untyped power in a local scalar equality did not simplify to the expected natural-number square.
Explicit real codomain and natural exponent in the local norm-square equality; all 111 public declarations and independent consumers are unchanged.
The [exact receipt](../../../../audits/r3-ehrenfest-b12c1e9b-failed/summary.json) is retained.
All seven packages remain candidates pending matching full and scoped audits.
