# MLB03 — `SingularClosure.invariantGalerkinRhs_inner`

Converts real Hilbert inner product against vector field into finite Fourier pairing.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinInvariant
```

[Raw cutout](../identities/MLB03.lean.txt) · [Full source context](../sources/S33_GalerkinInvariant.lean.txt) · [Pinned source, lines 164–188](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinInvariant.lean#L164-L188)

```lean
theorem invariantGalerkinRhs_inner (ν : ℝ) (N : ℕ) (z : InvariantGalerkinState N) :
    inner (𝕜 := ℝ) z (invariantGalerkinRhs ν N z) =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (star (hilbertCoeff N z.val k i) *
          galerkinRhs ν N (hilbertCoeff N z.val) k i).re := by
  change inner (𝕜 := ℝ) z.val (invariantGalerkinRhs ν N z).val = _
  rw [invariantGalerkinRhs_coe, PiLp.inner_apply]
  simp only [Complex.inner, ← Complex.star_def, Fintype.sum_prod_type]
  change (∑ k : ↥(cutoffModes N), ∑ i : Fin 3,
    (galerkinRhs ν N (hilbertCoeff N z.val) k.val i * star (z.val (k, i))).re) = _
  calc
    _ = ∑ k : ↥(cutoffModes N), ∑ i : Fin 3,
        (star (hilbertCoeff N z.val k.val i) *
          galerkinRhs ν N (hilbertCoeff N z.val) k.val i).re := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw [hilbertCoeff_apply]
      congr 1
      exact mul_comm _ _
    _ = _ := Finset.sum_coe_sort (cutoffModes N)
      (fun k => ∑ i : Fin 3,
        (star (hilbertCoeff N z.val k i) *
          galerkinRhs ν N (hilbertCoeff N z.val) k i).re)
```

## Context and reuse boundary

Combine energy splitting and cancellation to get the exact energy differential identity; this statement alone is an algebraic pairing identity.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `eeaf7acef88635864a09fa92ca07745c19a62912`. Cutout SHA-256: `d8979304bafe652ebb82beef506654e57be066dac8376ba66a48dd285772849d`.
