# Preprint review: version 1.1

**Status: ready for preprint circulation.** Reviewed on 19 November 2026.

Title: *Finite Fourier budgets and global continuation for the periodic
Navier–Stokes equations*. Author: Simon Suchan. Length: 16 A4 pages.

## Mathematical and editorial review

- The hypotheses, Fourier convention, pressure normalization and maximal
  lifetime are explicit before the main theorem. The full finite Fourier
  budget remains a hypothesis for general smooth data.
- The ten-step derivation is supported by numbered propositions and proofs.
  The quartic coefficient, viscosity scaling, Gronwall argument, uniform
  restart and strict cutoff passage were checked, including zero data,
  equality with the cutoff and infinite lifetime.
- The weak-solution representative, energy inequalities and all-times
  weak–strong comparison are specified. The cutoff proof identifies the
  separate numerical caloric admission theorem and preserves the same
  original weak witness through the tail and pressure splice.
- The smooth-data converse is proved analytically: the budget class equals
  the globally smooth class. This is a B-tier corollary, not an additional
  audited Lean endpoint. No universal budget bound, strict small-class
  inclusion or terminating initial-data test is asserted.
- Primary literature positioning distinguishes the classical continuation
  mechanism from the finite cutoff, same-witness composition and formal
  realization. Publication metadata and the cited results were checked.
- Independent agent mathematical and source reviews found no remaining
  substantive blocker after corrections. This is an editorial readiness
  judgment, not a claim of journal acceptance or human peer review.

## Formal correspondence and reproducibility

The displayed full root signature agrees with the pinned Lean source, up to
line wrapping. Every clickable declaration/line anchor was checked against
that source. Compiled fixed-constant small-data counterparts are distinguished
from freshly audited declarations and from the arbitrary-constant analytic
reconstruction. The explicit same-witness gluing module is identified as a
separately audited contextual realization; it is not misrepresented as a direct
import of the root.

The accepted proof remains at
`fdb515d8bde35ec8021bbc26f360aca8dfa2855c`, external run
[44566880192](https://github.com/randogelist/Methboke/actions/runs/44566880192).
Its recorded scope is 365 modules, 55 fresh audit packages, 265 named
signatures and axiom audits plus the QFB cutout, and 183 external controls.
The only recorded axioms are `propext`, `Classical.choice` and `Quot.sound`.

The original human evidence record at `6a4f86ff` and complete archive at
`8876af42` are cited separately from the proof revision. The preserved ZIP
contains all 129 original members, including the full report, all 55 fresh
package logs, the cutout and manifests. Its SHA-256 is
`ec7fbafac42924bc814b7a23f7c090b5f476d84d76193b5f4c0a100c3051612d`.

No Lean source or verification input was changed for this manuscript
revision. No new Lean compilation or kernel audit was run, locally or
externally. The mathematical converse does not alter the accepted endpoint.

## Production checks

- Two-pass pdfLaTeX build completed with no warnings, unresolved references,
  overfull boxes or missing glyphs.
- All fonts are embedded; page headers, footers and text bounds were checked.
- The rendered pages were visually reviewed, including the root signature,
  formal-anchor table, evidence appendix and bibliography.
- The final PDF and editable source are paired by SHA-256 in
  `MANUSCRIPT_MANIFEST.json`; the repository status records the same version.

The result is a self-contained mathematical preprint suitable for circulation.
The finite-budget hypothesis and the boundary of the formal verification
remain visible in the abstract, theorem, class characterization and appendices.
