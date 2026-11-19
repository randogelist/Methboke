# FAST05 — `SingularClosure.torusSobolevLeray_norm_le`

At s=0 contract Leray projection of residual; combine with finite cutoff contraction.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.FourierSobolevOperators
```

[Raw cutout](../identities/FAST05.lean.txt) · [Full source context](../sources/S20_FourierSobolevOperators.lean.txt) · [Pinned source, lines 364–365](https://github.com/randogelist/Methboke/blob/9ae4429b9c218c109bddaac2f993f1cc5bd66aa8/Material/_vendor/SingularClosure/FourierSobolevOperators.lean#L364-L365)

```lean
theorem torusSobolevLeray_norm_le (s : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevLeray s c‖ ≤ ‖c‖ := torusSobolevLerayLinear_norm_le s c
```

## Context and reuse boundary

Does not by itself identify physical Leray or project a physical residual. Need synthesis/Parseval adapters.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set
open scoped BigOperators ENNReal
namespace SingularClosure
noncomputable section
```

Weighted Fourier Sobolev map; physical Leray/cutoff identification is not provided by this line.

Earlier helpers noted by source review (not an exhaustive dependency list): `torusSobolevLeray`, `torusSobolevLerayLinear_norm_le`.

Source blob: `98bbd557c7014537ecb77d85475cd7b05c1cb1b5`. Cutout SHA-256: `80bb0bcbdf3a2d9e6022e2e77f448bcba3cfce6f892b4813de28172094f1deab`.
