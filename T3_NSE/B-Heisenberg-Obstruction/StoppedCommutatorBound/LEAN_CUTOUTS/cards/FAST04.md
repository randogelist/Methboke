# FAST04 — `SingularClosure.coefficientEnergy_le_dissipation`

Supply mean-zero finite Poincare estimate for cross convection terms after Parseval.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.PeriodicSobolev
```

[Raw cutout](../identities/FAST04.lean.txt) · [Full source context](../sources/S22_PeriodicSobolev.lean.txt) · [Pinned source, lines 305–313](https://github.com/randogelist/Methboke/blob/9ae4429b9c218c109bddaac2f993f1cc5bd66aa8/Material/_vendor/SingularClosure/PeriodicSobolev.lean#L305-L313)

```lean
theorem coefficientEnergy_le_dissipation (N : ℕ) (c : FourierCoeff) :
    coefficientEnergy N c ≤ coefficientDissipation N c := by
  have hgap : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  calc
    coefficientEnergy N c = 1 * coefficientEnergy N c := by ring
    _ ≤ 4 * Real.pi ^ 2 * coefficientEnergy N c :=
      mul_le_mul_of_nonneg_right hgap (coefficientEnergy_nonneg N c)
    _ ≤ coefficientDissipation N c := COEFFICIENT_POINCARE N c
```

## Context and reuse boundary

Need reality and physical/coefficient Parseval adapters for the real error field.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Metric
open scoped ContDiff ENNReal NNReal BigOperators
namespace SingularClosure
noncomputable section
```

No reality assumption needed for coefficient inequality; physical realization requires Parseval and reality. Zero mode is excluded by cutoffModes. Generic file variable F is unused in this theorem and is not a new theorem argument.

Earlier helpers noted by source review (not an exhaustive dependency list): `COEFFICIENT_POINCARE`, `coefficientEnergy_nonneg`.

Source blob: `704b8970c312368c6e64cb1700c9a9402e1d9604`. Cutout SHA-256: `9115d26b158cef780ad4438ad8e2b57d764e23c9639d5747b4f2a4727a66ddbb`.
