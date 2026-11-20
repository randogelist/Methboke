# MLB19 — `MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds`

Audited cutoff-uniform short-time H1/H2 bounds from physical smooth initial data and a bound on initial dissipation.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.LocalGalerkinBounds
```

[Raw cutout](../identities/MLB19.lean.txt) · [Full source context](../sources/S24_LocalGalerkinBounds.lean.txt) · [Pinned source, lines 160–210](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/LocalGalerkinBounds.lean#L160-L210)

```lean
theorem galerkin_uniform_local_sobolev_bounds
    (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R) :
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      (∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        ‖g.sobolevState 1 t‖ ^ 2 ≤ 4 * (R + 1)) ∧
      IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2)
        volume 0 (localGalerkinTime ν R) ∧
      (∫ t in (0 : ℝ)..(localGalerkinTime ν R), ‖g.sobolevState 2 t‖ ^ 2) ≤
        6 * (R + 1) * localGalerkinTime ν R + localGalerkinAccumulationBound ν R / ν := by
  intro N g
  let T : ℝ := localGalerkinTime ν R
  have hT : 0 ≤ T := (localGalerkinTime_pos hν hR).le
  have hb := galerkin_uniform_local_enstrophy_accumulation ν R hν hR a ha hinit N g
  have hiH2 : IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2) volume 0 T :=
    (((g.sobolevState_continuousOn 2).mono (fun t ht => ht.1)).norm.pow 2).intervalIntegrable_of_Icc hT
  have hiZ : IntervalIntegrable
      (fun t => coefficientLaplacianSquare N (g.coeff t)) volume 0 T :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
  have hZ : (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t)) ≤
      localGalerkinAccumulationBound ν R / ν := by
    have hacc := (hb T ⟨hT, le_rfl⟩).2
    have hD := coefficientDissipation_nonneg N (g.coeff T)
    apply (le_div_iff₀ hν).2
    nlinarith
  refine ⟨?_, hiH2, ?_⟩
  · intro t ht
    change ‖finiteSobolev 1 N (g.coeff t)‖ ^ 2 ≤ _
    rw [finiteSobolev_H1_norm_sq]
    have hD := (hb t ht).1
    have hE := coefficientEnergy_le_dissipation N (g.coeff t)
    linarith
  · calc
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤
          ∫ t in (0 : ℝ)..T, 6 * (R + 1) + coefficientLaplacianSquare N (g.coeff t) := by
        apply intervalIntegral.integral_mono_on hT hiH2 (intervalIntegrable_const.add hiZ)
        intro t ht
        change ‖finiteSobolev 2 N (g.coeff t)‖ ^ 2 ≤ _
        rw [finiteSobolev_H2_norm_sq]
        have hD := (hb t ht).1
        have hE := coefficientEnergy_le_dissipation N (g.coeff t)
        linarith
      _ = 6 * (R + 1) * T +
          ∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const hiZ,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      _ ≤ 6 * (R + 1) * T + localGalerkinAccumulationBound ν R / ν :=
        add_le_add le_rfl hZ
```

## Context and reuse boundary

Time is localGalerkinTime ν R; cannot extrapolate to all of [0,1/γ] without additional stability/iteration.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `db99eb577a0f397bc656b23a9e11c6ca6c2ed5d5`. Cutout SHA-256: `9116fdaca5eaccc5c9dc373bd854a834c628226d3bcdf5265014e7c8dbe09d49`.
