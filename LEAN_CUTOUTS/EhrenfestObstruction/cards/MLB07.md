# MLB07 — `SingularClosure.GalerkinSolution.coefficientEnergy_identity`

Exact coefficient-energy derivative E'=-2νD.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinEnergy
```

[Raw cutout](../identities/MLB07.lean.txt) · [Full source context](../sources/S31_GalerkinEnergy.lean.txt) · [Pinned source, lines 211–219](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinEnergy.lean#L211-L219)

```lean
theorem GalerkinSolution.coefficientEnergy_identity
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientEnergy N (g.coeff r))
      ((-2 * ν) * coefficientDissipation N (g.coeff t)) (Ici 0) t := by
  have hzero := coefficientNonlinearPower_eq_zero N (g.coeff t)
    (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht)
  simpa only [hzero, mul_zero, sub_zero] using
    g.coefficientEnergy_balance_with_remainder ht
```

## Context and reuse boundary

E is full squared L2 norm, not half energy; defined only on forward solution.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set
open scoped BigOperators
namespace SingularClosure
noncomputable section
```

Actual GalerkinSolution only; L2 energy control alone does not give the desired uniform H1 bound.

Earlier helpers noted by source review (not an exhaustive dependency list): `coefficientNonlinearPower_eq_zero`, `GalerkinSolution.coefficientEnergy_balance_with_remainder`.

Source blob: `e6501bff17d1fa9aa48166e85a1ddfafc7c221ae`. Cutout SHA-256: `e97d1eec1e8b16ac9607f0ec80adb8b364be0ea82ba800f0dcf3835a7eae86d9`.
