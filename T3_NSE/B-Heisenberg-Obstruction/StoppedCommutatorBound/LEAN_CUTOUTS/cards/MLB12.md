# MLB12 — `SingularClosure.canonicalGalerkinSolution`

Chooses the actual exact Galerkin family from one fixed smooth datum.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.CanonicalGalerkin
```

[Raw cutout](../identities/MLB12.lean.txt) · [Full source context](../sources/S27_CanonicalGalerkin.lean.txt) · [Pinned source, lines 15–17](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CanonicalGalerkin.lean#L15-L17)

```lean
def canonicalGalerkinSolution (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (N : ℕ) : GalerkinSolution ν a N :=
  (GALERKIN_GLOBAL_EXISTS_UNIQUE ν hν a ha N).choose
```

## Context and reuse boundary

Choice of a solution, not a new estimate. Do not vary datum with N.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SingularClosure
noncomputable section
```

Noncomputable choice from GALERKIN_GLOBAL_EXISTS_UNIQUE; not a formula executable by reduction. Keep ν,hν,a,ha fixed. Nonnegative-time guarantees only.

Earlier helpers noted by source review (not an exhaustive dependency list): `GALERKIN_GLOBAL_EXISTS_UNIQUE`.

Source blob: `e13bfcd457edef7a93af8f3fdacf963795a6c58c`. Cutout SHA-256: `a55ec0e320fd9d4f30833aa936cc4443f913a4e076a9133836158286f7db7c68`.
