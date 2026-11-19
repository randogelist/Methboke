# E01 retained source archive

Status: **PREPARED_SOURCE_ONLY**. This archive is an inactive candidate collection. No Lean, Lake, kernel audit, or external compiler was executed for this collection. Static review and text-level inventory checks do not establish elaboration or kernel acceptance.

The frozen collection contains 19 Lean files: 11 implementation modules, 7 exact-consumer modules, and 1 separate axiom-query module. It prepares 129 theorem candidates, 25 definitions, 3 abbreviations, 148 exact consumer examples, and 148 named axiom queries. All 129 theorem candidates have an explicit consumer and a named query. The other 19 queries inspect definitions. Six additional definitions are used transitively by queried constructions; no result of any query is asserted.

The mathematical interfaces are listed in `E01_COVERAGE.md`. They use the existing native finite real solenoidal phase, actual Fourier synthesis and physical cube integrals. The source package includes real orthonormal coordinates and phase-space volume, a two-way coefficient adapter, actual projected initial data, positive self-adjoint bounded Stokes, orthogonal cutoffs and Leray, derivative commutation, the nonsymmetric bilinear transport, actual smooth NSE right-hand side, and both spectral and physical energy cancellation.

The native cutoff is the nonzero Euclidean frequency ball. The proposed upper Stokes bound is `(2*pi)^2*N^2`; no cubical cutoff is assumed. Phase-space Lebesgue volume is distinct from physical spatial unit-cube volume. The Leray identification with the smaller real phase projection is used only after proving the relevant reality condition.

## Source provenance and verification boundary

Mathlib source pin: `db584cd6d46c92f209a44c0f1c829460d327499d`, with the project's Lean 4.33 source environment. Native source snapshots read for this collection include Methboke revisions `9ae4429b9c218c109bddaac2f993f1cc5bd66aa8` and `5b1d5e89754e82bb3867daefa1af4f887cadd33b` (transport's native reality proof). These are source provenance, not a claim of a successful build of this archive at either revision. The consuming repository commit, exact dependency lock, external compiler evidence, and axiom output must be recorded when this collection is activated.

The implementation imports use `MethbokeAddon.EhrenfestObstruction.*`. For an authorized external integration, each candidate file must be staged at its matching module path, and every exact-consumer and audit module must also be checked. The current archive intentionally retains separate source folders and contains no build-registration change. Source imports and declarations are recorded in `E01_SOURCE_MANIFEST.json`.

No local execution fallback is permitted. The exact consumer examples are prepared checks, not successful tests. The query source contains `#print axioms`; none of those commands has been run for this collection. No A-tier or completed external-milestone claim is made.

## Review scope

- `/root/qm_single_condition` independently reviewed `PhaseMultipliers`, `PhaseStokes`, `PhaseCutoffs`, and `PhaseBounds`, finding no material mathematical defect in the actual multiplier, Stokes, cutoff, and radial estimates.
- `/root/qm_single_condition` independently reviewed `PhaseLeray`; `/root/ehrenfest_error` also reviewed its residual orthogonality and exact projection consumer interface. Neither found a material mathematical defect.
- `/root/ehrenfest_mathlib_index` independently reviewed the transport author's `PhaseTransport` and `PhaseTransportPhysical` against the native coefficient and physical-pairing identities, finding no material mathematical defect.
- `PhaseSpace`, `PhaseSynthesis`, `PhaseVolume`, and `PhaseInitialState` have source/API inspection by their preparer. This document does not attribute an independent peer review to those four modules.

These are static mathematical/source reviews, not elaboration results. The manifest records exact file bytes and the prepared check coverage.

## Scope ends at E01

The collection represents the polynomial structure by an explicit linear-plus-bilinear decomposition, without claiming a separate Mathlib polynomial-object theorem. It does not assert one aggregate theorem named `REAL_SOLENOIDAL_GALERKIN_ALGEBRA`.

No E02 complete two-sided flow, joint smooth dependence, group law, inverse Jacobian, or identification with the canonical trajectory is supplied. No E03–E05 unitary-group, self-adjoint unbounded generator, Stone theorem, or Ehrenfest operator realization is supplied. The finite-dimensional bounded Stokes operator is not an unbounded transport Hamiltonian. No NSE obstruction or singular witness follows from this archive alone.

Frozen files must be revised as a new candidate version if external checking exposes an error. The scalar-root verification batches and repository sources were not modified while assembling this archive.
