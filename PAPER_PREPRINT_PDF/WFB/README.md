# WFB preprint draft

**A finite Fourier-budget criterion for global Navier-Stokes regularity on the three-torus**

Version 1.0, 19 November 2026. The manuscript follows the structure of the
[small-H1/2 publication](https://zenodo.org/records/24185514): abstract,
explicit normalization, numbered theorems and proofs, source-linked formal
appendices and references. The teal subtitle and links, running headers and
section-based equation numbering follow the reference presentation. Exact
original font metrics were not available; this is a typeset companion paper.

- [PDF](WFB_FOURIER_BUDGET_PREPRINT.pdf)
- [Editable LaTeX](WFB_FOURIER_BUDGET_PREPRINT.tex)
- [Ten-step mathematical source](../../WFB_TEN_STEP_PUBLICATION_DERIVATION_B_TIER.txt)
- [Accepted proof evidence](../../audits/material-fdb515d8/summary.json)

The finite full Fourier-budget hypothesis remains explicit. QFB provides an
additional same-original-trajectory tail; it is not attributed to the small-data
paper. The manuscript gives no universal smooth-data budget bound and no new
formal promotion. Its exposition steps are distinct from the ten implementation
obligations.

## Build

Use a standard TeX Live installation with pdfLaTeX and the packages declared
in the source. From this directory, run the following command twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error WFB_FOURIER_BUDGET_PREPRINT.tex
```

This is document typesetting only. No Lean, Lake or local kernel audit is
needed or authorized. No Lean sources or verification inputs were changed.
The accepted formal proof remains at commit
`fdb515d8bde35ec8021bbc26f360aca8dfa2855c`, external run 44566880192.

## Editorial checks

Mathematical review checked the coefficient 64*pi^4*delta, viscosity rescaling,
strict cutoff overlap (including equality), the zero and infinite-lifetime
cases, pressure normalization, and the same original weak witness. Source
review distinguished compiled fixed-constant small-data counterparts from
freshly audited roots and from the arbitrary-constant analytic reconstruction.
The final PDF is checked for unresolved references, overflowing text and
missing glyphs, and its pages are visually reviewed.
