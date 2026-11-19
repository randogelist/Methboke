# MLB11 — `SingularClosure.GalerkinSolution.sobolevState_H1_physical_norm_sq`

Exact bridge from abstract H1 coefficient norm to physical L2 plus gradient square.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.TorusGalerkinSobolev
```

[Raw cutout](../identities/MLB11.lean.txt) · [Full source context](../sources/S36_TorusGalerkinSobolev.lean.txt) · [Pinned source, lines 135–141](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/TorusGalerkinSobolev.lean#L135-L141)

```lean
theorem GalerkinSolution.sobolevState_H1_physical_norm_sq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖g.sobolevState 1 t‖ ^ 2 =
      (∫ x in unitCube, ‖g.velocity t x‖ ^ 2) +
        ∫ x in unitCube, gradientSquareDensity (g.velocity t) x :=
  finiteSobolev_H1_physical_norm_sq N (g.coeff t) (g.real_symmetry t ht)
```

## Context and reuse boundary

Use to transfer an independently established uniform H1 bound; no such bound is supplied by this identity.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace SingularClosure
noncomputable section
```

Displayed endpoint is trajectory-specific. Its earlier arbitrary-coefficient helper finiteSobolev_H1_physical_norm_sq is the actual adapter for an error coefficient family; expose that helper separately if used, without inventing audit status.

Earlier helpers noted by source review (not an exhaustive dependency list): `finiteSobolev_H1_physical_norm_sq`, `finiteSobolev`, `GalerkinSolution.sobolevState`.

Source blob: `2ee17b11e2417a19a05a14a6b170e68397ce26f2`. Cutout SHA-256: `8fa5db26cab63fb359dcfc6d4eeab12ea811f65ad91f5e78d55890a3dc0a2720`.
