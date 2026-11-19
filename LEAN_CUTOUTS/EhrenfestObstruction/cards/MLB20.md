# MLB20 — `MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise`

Audited all-order pointwise Galerkin bounds conditional on a uniform integrated H2 bound.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.LocalGalerkinRegularity
```

[Raw cutout](../identities/MLB20.lean.txt) · [Full source context](../sources/S25_LocalGalerkinRegularity.lean.txt) · [Pinned source, lines 87–102](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/LocalGalerkinRegularity.lean#L87-L102)

```lean
theorem local_galerkin_high_order_pointwise
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState m t‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := local_galerkin_high_order_accumulation ν hν a ha T hT S hS hH2 m
  refine ⟨B, hB, ?_⟩
  intro N hN g t ht
  have hi : 0 ≤ ∫ r in (0 : ℝ)..t, ‖g.sobolevState (m + 1) r‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => sq_nonneg _)
  have h := hb N hN g t ht
  nlinarith [mul_nonneg hν.le hi]
```

## Context and reuse boundary

The hH2 hypothesis is substantive. This theorem cannot be used to manufacture the missing smooth-front=>uniform-Galerkin bound.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `95e5f38462638e5431e128252585a87e54f37ce4`. Cutout SHA-256: `2739bd099453801c11010e506e8b70142efc4c66cf561631af99c44ec0a16598`.
