import MethbokeAddon.QuasiFeffermanA.PhysicalH1

/-!
# Actual L2 trace of the physical weak gradient

Embed the scalar divergence in the fixed nonzero first coordinate vector.
The sum of concrete coordinate slices of the supplied first derivatives
vanishes exactly when the original field satisfies every native compact
solenoidal test. The proof derives the integration-by-parts relation from
the actual weak-gradient identities and proves test separation in L2.

There is no assumed divergence interface or sector-commutation premise in
the criterion. Sector naturality and its use on solenoidal H1 are separate.
Prepared source requires matching external evidence; no local Lean is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff

namespace MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence

open QFA.Endpoints.Representation

/-- The j-th real coordinate placed in the fixed first coordinate direction. -/
def coordinateSliceVectorCLM (j : Fin 3) : Space →L[ℝ] Space :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).smulRight (coordinateVector 0)

@[simp] theorem coordinateSliceVectorCLM_apply (j : Fin 3) (v : Space) :
    coordinateSliceVectorCLM j v = (v j) • coordinateVector 0 := rfl

/-- The actual full-volume L2 lift of the bounded coordinate slice. -/
def coordinateSliceL2 (j : Fin 3) : SpatialL2 →L[ℝ] SpatialL2 :=
  (coordinateSliceVectorCLM j).compLpL 2 volume

theorem coordinateSliceL2_ae (j : Fin 3) (v : SpatialL2) :
    (fun x : Space => coordinateSliceL2 j v x) =ᵐ[volume]
      (fun x : Space => coordinateSliceVectorCLM j (v x)) :=
  (coordinateSliceVectorCLM j).coeFn_compLpL v

/-- The actual scalar weak divergence, embedded along a fixed nonzero vector. -/
def spatialGradientTrace (G : Fin 3 → SpatialL2) : SpatialL2 :=
  ∑ j : Fin 3, coordinateSliceL2 j (G j)

theorem spatialGradientTrace_ae (G : Fin 3 → SpatialL2) :
    (fun x : Space => spatialGradientTrace G x) =ᵐ[volume]
      (fun x : Space => (∑ j : Fin 3, (G j x) j) • coordinateVector 0) := by
  have hall : ∀ᵐ x : Space ∂volume, ∀ j : Fin 3,
      coordinateSliceL2 j (G j) x = coordinateSliceVectorCLM j (G j x) :=
    ae_all_iff.mpr (fun j => coordinateSliceL2_ae j (G j))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Fin 3 => coordinateSliceL2 j (G j)), hall] with x hsum hx
  change (∑ j : Fin 3, coordinateSliceL2 j (G j)) x = _
  rw [hsum]
  simp_rw [hx, coordinateSliceVectorCLM_apply]
  exact (Finset.sum_smul ..).symm

/-- Compact test pairing commutes with a concrete coordinate slice. -/
theorem compactPairing_coordinateSlice (j : Fin 3) (ψ : Space → ℝ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) (v : SpatialL2) :
    compactPairingCLM ψ hψ hcompact (coordinateSliceL2 j v) =
      coordinateSliceVectorCLM j (compactPairingCLM ψ hψ hcompact v) := by
  rw [compactPairingCLM_apply, compactPairingCLM_apply]
  calc
    (∫ x : Space, ψ x • coordinateSliceL2 j v x) =
        ∫ x : Space, coordinateSliceVectorCLM j (ψ x • v x) := by
      apply integral_congr_ae
      filter_upwards [coordinateSliceL2_ae j v] with x hx
      rw [hx, map_smul]
    _ = coordinateSliceVectorCLM j (∫ x : Space, ψ x • v x) :=
      (coordinateSliceVectorCLM j).integral_comp_comm
        (integrable_compact_test_smul v hψ hcompact)

private theorem sum_coordinateSlice_derivative_integral
    (v : SpatialL2) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcompact : HasCompactSupport ψ) :
    (∑ j : Fin 3, coordinateSliceVectorCLM j
      (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) =
        (∫ x : Space, inner ℝ (v x) (scalarGradient ψ x)) • coordinateVector 0 := by
  have hint (j : Fin 3) :
      Integrable (fun x : Space => fderiv ℝ ψ x (coordinateVector j) • v x) volume :=
    integrable_compact_test_smul v
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcompact.fderiv_apply ℝ (coordinateVector j))
  calc
    (∑ j : Fin 3, coordinateSliceVectorCLM j
        (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) =
        ∑ j : Fin 3, ∫ x : Space,
          coordinateSliceVectorCLM j (fderiv ℝ ψ x (coordinateVector j) • v x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ((coordinateSliceVectorCLM j).integral_comp_comm (hint j)).symm
    _ = ∫ x : Space, ∑ j : Fin 3,
        coordinateSliceVectorCLM j (fderiv ℝ ψ x (coordinateVector j) • v x) := by
      exact (integral_finsetSum Finset.univ
        (fun j _ => (coordinateSliceVectorCLM j).integrable_comp (hint j))).symm
    _ = ∫ x : Space, inner ℝ (v x) (scalarGradient ψ x) • coordinateVector 0 := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [coordinateSliceVectorCLM_apply, PiLp.smul_apply, smul_eq_mul,
        ← Finset.sum_smul]
      congr 1
    _ = _ := integral_smul_const _ _

/-- Actual weak-gradient integration by parts identifies the vector L2 trace
with the native divergence test functional. All pairings are integrable. -/
theorem spatialWeakGradient_trace_pairing
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (hweak : SpatialWeakGradient v G)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcompact : HasCompactSupport ψ) :
    compactPairingCLM ψ hψ.continuous hcompact (spatialGradientTrace G) =
      -((∫ x : Space, inner ℝ (v x) (scalarGradient ψ x)) • coordinateVector 0) := by
  calc
    compactPairingCLM ψ hψ.continuous hcompact (spatialGradientTrace G) =
        ∑ j : Fin 3, coordinateSliceVectorCLM j (∫ x : Space, ψ x • G j x) := by
      rw [spatialGradientTrace, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [compactPairing_coordinateSlice, compactPairingCLM_apply]
    _ = -(∑ j : Fin 3, coordinateSliceVectorCLM j
        (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have htest : (∫ x : Space, ψ x • G j x) =
          -(∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x) := by
        simpa only [neg_neg] using congrArg Neg.neg (hweak j ψ hψ hcompact).symm
      rw [htest, map_neg]
    _ = _ := by rw [sum_coordinateSlice_derivative_integral v ψ hψ hcompact]

/-- The compact-test solenoidal condition is exactly zero actual L2 trace of
the physical weak gradient. No Fourier or projector premise is used. -/
theorem spatialWeakGradient_solenoidal_iff_trace_eq_zero
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (hweak : SpatialWeakGradient v G) :
    Solenoidal v ↔ spatialGradientTrace G = 0 := by
  constructor
  · intro hsol
    apply Lp.ext
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp (spatialGradientTrace G)).locallyIntegrable (by norm_num))
      ((Lp.memLp (0 : SpatialL2)).locallyIntegrable (by norm_num))
    intro ψ hψ hcompact
    rw [← compactPairingCLM_apply ψ hψ.continuous hcompact,
      ← compactPairingCLM_apply ψ hψ.continuous hcompact,
      spatialWeakGradient_trace_pairing hweak ψ hψ hcompact,
      (hsol ψ hψ hcompact).2, zero_smul, neg_zero, map_zero]
  · intro htrace ψ hψ hcompact
    refine ⟨integrable_solenoidalTest ⟨ψ, hψ, hcompact⟩ v, ?_⟩
    have h := spatialWeakGradient_trace_pairing hweak ψ hψ hcompact
    rw [htrace, map_zero] at h
    have hz : ((∫ x : Space, inner ℝ (v x) (scalarGradient ψ x)) •
        coordinateVector 0) = 0 := by
      exact neg_eq_zero.mp h.symm
    have hcoord := congrArg (fun z : Space => z 0) hz
    simpa [coordinateVector, PiLp.smul_apply] using hcoord

end MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence
