# MLB01 — `SingularClosure.invariantGalerkinSubspace`

Real Hilbert submodule whose elements satisfy Fourier reality and solenoidality; use InvariantGalerkinState N (line 106) as V_N.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinInvariant
```

[Raw cutout](../identities/MLB01.lean.txt) · [Full source context](../sources/S33_GalerkinInvariant.lean.txt) · [Pinned source, lines 73–104](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinInvariant.lean#L73-L104)

```lean
def invariantGalerkinSubspace (N : ℕ) : Submodule ℝ (GalerkinHilbertState N) where
  carrier := {z | SpectralReality (hilbertCoeff N z) ∧
    SpectralSolenoidal (hilbertCoeff N z)}
  zero_mem' := by
    change SpectralReality (hilbertCoeff N 0) ∧ SpectralSolenoidal (hilbertCoeff N 0)
    rw [hilbertCoeff_zero]
    constructor
    · intro k i
      simp
    · intro k
      simp
  add_mem' := by
    intro z w hz hw
    change SpectralReality (hilbertCoeff N (z + w)) ∧
      SpectralSolenoidal (hilbertCoeff N (z + w))
    rw [hilbertCoeff_add]
    constructor
    · intro k i
      simpa using congrArg₂ (· + ·) (hz.1 k i) (hw.1 k i)
    · intro k
      simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hz.2 k, hw.2 k,
        add_zero] using (add_zero (0 : ℂ))
  smul_mem' := by
    intro r z hz
    change SpectralReality (hilbertCoeff N (r • z)) ∧
      SpectralSolenoidal (hilbertCoeff N (r • z))
    rw [hilbertCoeff_smul]
    constructor
    · intro k i
      simp only [Pi.smul_apply, star_smul, star_trivial, hz.1 k i]
    · intro k
      simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, hz.2 k, smul_zero]
```

## Context and reuse boundary

Definition only. Need real finite-dimensional coordinate/volume adapter; ambient unrestricted complex coefficients are not the physical phase space.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `eeaf7acef88635864a09fa92ca07745c19a62912`. Cutout SHA-256: `e2687aabcff1b361135d79e452ccd6146c1ca2d01ea17316e397c63b30f5a262`.
