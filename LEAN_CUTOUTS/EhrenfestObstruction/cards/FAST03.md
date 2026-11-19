# FAST03 — `SingularClosure.torusSobolevMultiplierLinear_norm_le`

With high-frequency tail symbol, s=1 and t=2, obtain H1 tail O(1/N).

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.FourierSobolevOperators
```

[Raw cutout](../identities/FAST03.lean.txt) · [Full source context](../sources/S20_FourierSobolevOperators.lean.txt) · [Pinned source, lines 177–195](https://github.com/randogelist/Methboke/blob/9ae4429b9c218c109bddaac2f993f1cc5bd66aa8/Material/_vendor/SingularClosure/FourierSobolevOperators.lean#L177-L195)

```lean
theorem torusSobolevMultiplierLinear_norm_le (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    ‖torusSobolevMultiplierLinear s t b B hB hb c‖ ≤ B * ‖c‖ := by
  calc
    _ = ‖torusSobolevRepr s (torusSobolevMultiplierLinear s t b B hB hb c)‖ :=
      ((torusSobolevRepr s).norm_map _).symm
    _ ≤ ‖(B : ℂ) • torusSobolevRepr t c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [torusSobolevRepr_apply, torusSobolevMultiplierLinear_coeff]
      change ‖sobolevWeightedCoeff s (fun k i => b k * c.val k i) ki‖ ≤
        ‖(B : ℂ) * sobolevWeightedCoeff t c.val ki‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
      exact torusSobolev_multiplier_weighted_norm_le s t b B hb c.val ki
    _ = _ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB,
        (torusSobolevRepr t).norm_map]
```

## Context and reuse boundary

Need explicit tail symbol cutoff comparison, zero-mode agreement, and physical/Fourier norm bridge.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set
open scoped BigOperators ENNReal
namespace SingularClosure
noncomputable section
```

Explicit symbol bound hb required for every frequency. Mean-zero zero-mode agreement, cutoff comparison and physical norm realization remain new.

Earlier helpers noted by source review (not an exhaustive dependency list): `torusSobolevMultiplierLinear`, `torusSobolevMultiplierLinear_coeff`, `torusSobolev_multiplier_weighted_norm_le`.

Source blob: `98bbd557c7014537ecb77d85475cd7b05c1cb1b5`. Cutout SHA-256: `76ca380481ad1cc2c489736d52ba169fb695995f7d047887635528ad7160ccb3`.
