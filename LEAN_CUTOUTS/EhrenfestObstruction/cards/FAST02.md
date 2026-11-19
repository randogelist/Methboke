# FAST02 — `SingularClosure.FINITE_FOURIER_H2_L1_BOUND`

Bound projected reference C1 norm by H3 Fourier norm, applying H2-to-l1 separately to components and first derivative coefficients.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.LatticeSobolevSummability
```

[Raw cutout](../identities/FAST02.lean.txt) · [Full source context](../sources/S21_LatticeSobolevSummability.lean.txt) · [Pinned source, lines 121–125](https://github.com/randogelist/Methboke/blob/9ae4429b9c218c109bddaac2f993f1cc5bd66aa8/Material/_vendor/SingularClosure/LatticeSobolevSummability.lean#L121-L125)

```lean
theorem FINITE_FOURIER_H2_L1_BOUND : ∃ C : ℝ, 0 < C ∧
    ∀ (s : Finset Frequency) (a : Frequency → ℂ),
      (∑ k ∈ s, ‖a k‖) ^ 2 ≤ C *
        (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖a k‖) ^ 2) :=
  ⟨latticeSobolevConstant, latticeSobolevConstant_pos, finite_l1_sq_le_H2_sq⟩
```

## Context and reuse boundary

Need component/derivative symbol adapters and uniform reference H3 bound. The theorem is not itself a physical C1 estimate.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
set_option Elab.async true
open Set Module
open scoped BigOperators
namespace SingularClosure
noncomputable section
```

Scalar complex coefficient family over arbitrary finite frequency set; not directly vector C1. Square norm and torus Sobolev weight normalization must be retained.

Earlier helpers noted by source review (not an exhaustive dependency list): `latticeSobolevConstant`, `latticeSobolevConstant_pos`, `finite_l1_sq_le_H2_sq`.

Source blob: `256ed4881539d214137116a01483050831dbd48f`. Cutout SHA-256: `da6c5b48ce2fe4c116b17a2b131e77fb2dafc314ec6fb10d90961ac0764518c9`.
