# AUX01 — `SingularClosure.finiteSobolev_H1_physical_norm_sq`

Arbitrary-coefficient H1/physical norm identity for a spectrally real finite error; unlike MLB11 it has no GalerkinSolution premise.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.TorusGalerkinSobolev
```

[Raw cutout](../identities/AUX01.lean.txt) · [Full source context](../sources/S36_TorusGalerkinSobolev.lean.txt) · [Pinned source, lines 97–105](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/TorusGalerkinSobolev.lean#L97-L105)

```lean
theorem finiteSobolev_H1_physical_norm_sq (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    ‖finiteSobolev 1 N c‖ ^ 2 =
      (∫ x in unitCube, ‖finiteSynthesis N c x‖ ^ 2) +
        ∫ x in unitCube, gradientSquareDensity (finiteSynthesis N c) x := by
  rw [finiteSobolev_H1_norm_sq,
    ← FINITE_PHYSICAL_ENERGY_PARSEVAL N c hreal,
    ← FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal,
    physicalEnergy_eq_integral_norm_sq]
```

## Context and reuse boundary

Requires spectral reality and the actual finite-synthesis field; it does not prove any error evolution.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `2ee17b11e2417a19a05a14a6b170e68397ce26f2`. Cutout SHA-256: `763e7f068aad138bc82721e7035153e3e700ee637b6943d1047ae4a8de6779ee`.
