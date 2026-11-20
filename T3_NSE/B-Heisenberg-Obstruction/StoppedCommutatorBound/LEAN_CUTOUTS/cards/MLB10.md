# MLB10 — `SingularClosure.GalerkinSolution.coefficientDissipation_initial_le`

Uniform initial enstrophy bound D_N(0)<=D(a).

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.InitialCutoffBounds
```

[Raw cutout](../identities/MLB10.lean.txt) · [Full source context](../sources/S34_InitialCutoffBounds.lean.txt) · [Pinned source, lines 199–204](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/InitialCutoffBounds.lean#L199-L204)

```lean
theorem GalerkinSolution.coefficientDissipation_initial_le
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (ha : SmoothSigmaZero a) :
    coefficientDissipation N (g.coeff 0) ≤ ∫ x in unitCube, gradientSquareDensity a x := by
  rw [g.coefficientDissipation_initial_eq]
  exact coefficientDissipation_initial_cutoff_le N a ha.smooth ha.periodic
```

## Context and reuse boundary

Does not prove time-uniform enstrophy or any stopped commutator bound.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace SingularClosure
noncomputable section
```

Only t=0; cannot propagate the uniform initial bound across a full time slab.

Earlier helpers noted by source review (not an exhaustive dependency list): `GalerkinSolution.coefficientDissipation_initial_eq`, `coefficientDissipation_initial_cutoff_le`.

Source blob: `dadf69927b1858ab267cd1d1c5c629abdcf1dd33`. Cutout SHA-256: `8f9792be137d5fc618be6b100b8b0119b794ac7bc6566faaa59c2335d1883c5f`.
