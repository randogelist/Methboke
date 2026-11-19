# MLB06 — `SingularClosure.coefficientNonlinearPower_eq_zero`

Exact nonlinear energy cancellation under support, Fourier reality and solenoidality.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinEnergy
```

[Raw cutout](../identities/MLB06.lean.txt) · [Full source context](../sources/S31_GalerkinEnergy.lean.txt) · [Pinned source, lines 188–208](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinEnergy.lean#L188-L208)

```lean
theorem coefficientNonlinearPower_eq_zero
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : ∀ k : Frequency, ∀ i : Fin 3, c (-k) i = star (c k i))
    (hsol : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * c k i) = 0) :
    coefficientNonlinearPower N c = 0 := by
  have h := congrArg Complex.re
    (coefficientTransport_complex_energy_zero N c hsupp hreal hsol)
  unfold coefficientNonlinearPower
  simp only [Complex.re_sum, Complex.zero_re] at h
  calc
    _ = ∑ k ∈ cutoffModes N,
        (∑ i : Fin 3, star (c k i) *
          coefficientLeray k (coefficientTransport N c k) i).re := by
            simp only [Complex.re_sum]
    _ = ∑ k ∈ cutoffModes N,
        (∑ i : Fin 3, star (c k i) * coefficientTransport N c k i).re := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [coefficientLeray_pairing k (c k) (coefficientTransport N c k) (hsol k)]
    _ = 0 := by simpa only [Complex.re_sum] using h
```

## Context and reuse boundary

All three spectral premises must be carried from invariant state; cannot apply to arbitrary complex coefficients.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set
open scoped BigOperators
namespace SingularClosure
noncomputable section
```

Energy cancellation is not enstrophy cancellation; it does not remove coefficientEnstrophyNonlinearPower.

Earlier helpers noted by source review (not an exhaustive dependency list): `coefficientTransport_complex_energy_zero`, `coefficientLeray_pairing`.

Source blob: `e6501bff17d1fa9aa48166e85a1ddfafc7c221ae`. Cutout SHA-256: `a622fb7ec1411895a161eec46bfcc7550a7520639016bf282456c42728390cd6`.
