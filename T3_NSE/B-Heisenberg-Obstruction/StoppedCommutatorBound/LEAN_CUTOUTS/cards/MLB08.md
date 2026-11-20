# MLB08 — `SingularClosure.GalerkinSolution.coefficientEnstrophy_identity`

Exact D'=-2νZ-2P; frozen e=D/2, W=-P gives e'=W-νZ.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.EnstrophyInequality
```

[Raw cutout](../identities/MLB08.lean.txt) · [Full source context](../sources/S29_EnstrophyInequality.lean.txt) · [Pinned source, lines 86–93](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/EnstrophyInequality.lean#L86-L93)

```lean
theorem GalerkinSolution.coefficientEnstrophy_identity
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r))
      ((-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
        2 * coefficientEnstrophyNonlinearPower N (g.coeff t)) (Ici 0) t := by
  rw [← coefficientDissipation_rate_split]
  exact g.coefficientDissipation_hasDerivWithinAt ht
```

## Context and reuse boundary

Preserve the 1/2 normalization and sign of coefficientEnstrophyNonlinearPower.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
set_option Elab.async true
open Set
open scoped BigOperators
namespace SingularClosure
noncomputable section
```

Applies to GalerkinSolution only and gives HasDerivWithinAt on Ici 0. It does not apply to forced difference w_N. Preserve sign and factor two.

Earlier helpers noted by source review (not an exhaustive dependency list): `coefficientLaplacianSquare`, `coefficientEnstrophyNonlinearPower`, `coefficientDissipation_rate_split`, `GalerkinSolution.coefficientDissipation_hasDerivWithinAt`.

Source blob: `fdc12e4676295ea43d0e2f8d1f0592e0c545200e`. Cutout SHA-256: `659747f37b73dd72a31b9e35bf36f337ce3d9d5b9bf27799eb266f54e6dca925`.
