# MLB13 — `SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE`

Audited exact global forward Galerkin existence/uniqueness from spectral reality and solenoidality.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.CriticalGalerkin
```

[Raw cutout](../identities/MLB13.lean.txt) · [Full source context](../sources/S28_CriticalGalerkin.lean.txt) · [Pinned source, lines 124–139](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalGalerkin.lean#L124-L139)

```lean
theorem CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE
    (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ) :
    ∃ g : GalerkinSolution ν (finiteSynthesis N c) N,
      g.coeff 0 = cutoffCoeff N c ∧
        ∀ h : GalerkinSolution ν (finiteSynthesis N c) N,
          EqOn g.coeff h.coeff (Ici 0) := by
  have hrealN : SpectralReality (datumFourierCoeff (finiteSynthesis N c)) := by
    rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N c hreal]
    exact cutoffCoeff_preserves_reality N hreal
  have hsolN : SpectralSolenoidal (datumFourierCoeff (finiteSynthesis N c)) := by
    rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N c hreal]
    exact cutoffCoeff_preserves_solenoidal N hsol
  obtain ⟨g⟩ := galerkinSolution_exists_of_fourier_invariants ν hν
    (finiteSynthesis N c) N (criticalGalerkin_fourier_integrable N c) hrealN hsolN
  exact ⟨g, criticalGalerkin_initial_coeff hreal g, fun h => g.coeff_unique_forward h⟩
```

## Context and reuse boundary

Forward only; its admission and native finite-synthesis initial datum remain literal.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `b2aa366cdfaadeb48b369da21267f2d9f9d4351f`. Cutout SHA-256: `29f05489f6ced13663690fdd5fdaa6507c68020c4e46a19156dd1a2ae3a1e5c3`.
