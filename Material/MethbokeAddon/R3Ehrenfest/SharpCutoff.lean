import MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
import MethbokeAddon.QuasiFeffermanA.LeraySolenoidal

/-!
# The actual sharp Fourier cutoff on real whole-space L2 and physical H1

The multiplier is the characteristic function of the closed frequency ball
of radius `n + 1`. Its measurability, real even symmetry and bound are proved
from that formula. The existing real Fourier multiplier construction supplies
the operator; no abstract projection or assumed preservation port is used.

This file establishes contraction, idempotence, self-adjointness, commutation
with the actual Leray projection, and transport of supplied native weak
gradients. The H1 lift acts on the existing physical weak-gradient graph.
It does not assert construction of new derivatives for arbitrary L2 inputs,
a bandlimited flow, a Navier--Stokes solution, or an obstruction theorem.

Prepared source requires matching authorized cached external type and axiom
evidence. No local Lean, Lake, kernel audit or proof runner is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal

namespace MethbokeAddon.R3Ehrenfest.SharpCutoff

open MethbokeAddon.QuasiFeffermanA
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealFourier RealEvenMultipliers LerayMultiplier LerayH1 LeraySolenoidal

/-- Positive radii tending through the natural numbers, with no zero-radius case. -/
def cutoffRadius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem cutoffRadius_pos (n : ℕ) : 0 < cutoffRadius n := by
  unfold cutoffRadius
  positivity

/-- The literal sharp closed-ball symbol, with its boundary included. -/
def cutoffValue (n : ℕ) (ξ : Space) : ℝ :=
  if ‖ξ‖ ≤ cutoffRadius n then 1 else 0

theorem measurable_cutoffValue (n : ℕ) : Measurable (cutoffValue n) := by
  exact Measurable.ite (isClosed_le continuous_norm continuous_const).measurableSet
    measurable_const measurable_const

theorem cutoffValue_neg (n : ℕ) (ξ : Space) :
    cutoffValue n (-ξ) = cutoffValue n ξ := by
  simp only [cutoffValue, norm_neg]

theorem norm_cutoffValue_le (n : ℕ) (ξ : Space) : ‖cutoffValue n ξ‖ ≤ 1 := by
  by_cases h : ‖ξ‖ ≤ cutoffRadius n <;> simp [cutoffValue, h]

theorem cutoffValue_mul_self (n : ℕ) (ξ : Space) :
    cutoffValue n ξ * cutoffValue n ξ = cutoffValue n ξ := by
  by_cases h : ‖ξ‖ ≤ cutoffRadius n <;> simp [cutoffValue, h]

/-- A constructed real, even, measurable symbol with exact bound one. -/
def cutoffSymbol (n : ℕ) : RealEvenSymbol where
  value := cutoffValue n
  measurable := measurable_cutoffValue n
  even := cutoffValue_neg n
  bound := 1
  norm_le := norm_cutoffValue_le n

/-- The actual real L2 Fourier cutoff, as a continuous real-linear map. -/
def sharpCutoff (n : ℕ) : SpatialL2 →L[ℝ] SpatialL2 :=
  realFourierMultiplierCLM (cutoffSymbol n)

@[simp] theorem sharpCutoff_apply (n : ℕ) (u : SpatialL2) :
    sharpCutoff n u = realFourierMultiplier (cutoffSymbol n) u := rfl

/-- The output has precisely the prescribed Fourier transform almost everywhere. -/
theorem sharpCutoff_fourier_ae (n : ℕ) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space =>
        (cutoffValue n ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  fourier_complexify_realFourierMultiplier_ae (cutoffSymbol n) u

/-- Frequencies beyond the actual cutoff radius vanish, with no support premise. -/
theorem sharpCutoff_fourier_outside (n : ℕ) (u : SpatialL2) :
    ∀ᵐ ξ : Space ∂volume, cutoffRadius n < ‖ξ‖ →
      (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ = 0 := by
  filter_upwards [sharpCutoff_fourier_ae n u] with ξ hξ
  intro hout
  rw [hξ]
  simp [cutoffValue, not_le.mpr hout]

theorem norm_sharpCutoff_le (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoff n u‖ ≤ ‖u‖ := by
  change ‖realFourierMultiplier (cutoffSymbol n) u‖ ≤ ‖u‖
  simpa only [cutoffSymbol, NNReal.coe_one, one_mul] using
    norm_realFourierMultiplier_le (cutoffSymbol n) u

theorem sharpCutoff_idempotent (n : ℕ) (u : SpatialL2) :
    sharpCutoff n (sharpCutoff n u) = sharpCutoff n u := by
  apply complexifyL2LI.injective
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change (𝓕 (complexifyL2 (sharpCutoff n (sharpCutoff n u))) : ComplexL2) =
    (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2)
  apply Lp.ext
  filter_upwards [sharpCutoff_fourier_ae n (sharpCutoff n u),
    sharpCutoff_fourier_ae n u] with ξ ho hi
  rw [ho, hi]
  by_cases h : ‖ξ‖ ≤ cutoffRadius n <;> simp [cutoffValue, h]

private theorem inner_frequencyCutoff_left (n : ℕ) (f g : ComplexL2) :
    inner ℂ (frequencyMultiplier (cutoffSymbol n) f) g =
      inner ℂ f (frequencyMultiplier (cutoffSymbol n) g) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencyMultiplier_ae (cutoffSymbol n) f,
    frequencyMultiplier_ae (cutoffSymbol n) g] with ξ hf hg
  rw [hf, hg]
  by_cases h : ‖ξ‖ ≤ cutoffRadius n <;> simp [cutoffSymbol, cutoffValue, h]

private theorem real_inner_complexify (u v : SpatialL2) :
    inner ℝ u v = Complex.re (inner ℂ (complexifyL2 u) (complexifyL2 v)) := by
  letI : InnerProductSpace ℝ ComplexL2 := InnerProductSpace.rclikeToReal ℂ ComplexL2
  exact (complexifyL2LI.inner_map_map u v).symm

/-- Self-adjointness in the original real L2 inner product. -/
theorem inner_sharpCutoff_left (n : ℕ) (u v : SpatialL2) :
    inner ℝ (sharpCutoff n u) v = inner ℝ u (sharpCutoff n v) := by
  rw [real_inner_complexify, real_inner_complexify]
  apply congrArg Complex.re
  rw [← Lp.inner_fourier_eq (complexifyL2 (sharpCutoff n u)) (complexifyL2 v),
    ← Lp.inner_fourier_eq (complexifyL2 u) (complexifyL2 (sharpCutoff n v))]
  simp only [sharpCutoff_apply, fourier_complexify_realFourierMultiplier]
  exact inner_frequencyCutoff_left n (𝓕 (complexifyL2 u)) (𝓕 (complexifyL2 v))

/-- The concrete scalar cutoff commutes with the concrete whole-space Leray map. -/
theorem sharpCutoff_realLeray (n : ℕ) (u : SpatialL2) :
    sharpCutoff n (realLeray u) = realLeray (sharpCutoff n u) := by
  apply complexifyL2LI.injective
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change (𝓕 (complexifyL2 (sharpCutoff n (realLeray u))) : ComplexL2) =
    (𝓕 (complexifyL2 (realLeray (sharpCutoff n u))) : ComplexL2)
  apply Lp.ext
  filter_upwards [sharpCutoff_fourier_ae n (realLeray u), realLeray_fourier_ae u,
    realLeray_fourier_ae (sharpCutoff n u), sharpCutoff_fourier_ae n u]
    with ξ ho hi ht hf
  rw [ho, hi, ht, hf, map_smul]

/-- Native weak solenoidality is preserved on all of real L2. -/
theorem solenoidal_sharpCutoff (n : ℕ) (u : SpatialL2) (hu : Solenoidal u) :
    Solenoidal (sharpCutoff n u) := by
  apply (realLeray_eq_self_iff_solenoidal (sharpCutoff n u)).mp
  rw [← sharpCutoff_realLeray, (realLeray_eq_self_iff_solenoidal u).mpr hu]

/-- Each supplied weak derivative is transported by the same actual cutoff. -/
theorem spatialWeakGradient_sharpCutoff (n : ℕ)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    SpatialWeakGradient (sharpCutoff n v) (fun j => sharpCutoff n (G j)) :=
  spatialWeakGradient_realFourierMultiplier (cutoffSymbol n) h

/-- The cutoff on the existing physical H1 graph, using its native weak gradients. -/
def physicalH1SharpCutoff (n : ℕ) (u : PhysicalH1) : PhysicalH1 :=
  physicalH1OfWeakGradient (sharpCutoff n (physicalH1Velocity u))
    (fun j => sharpCutoff n (physicalH1Gradient j u))
    (spatialWeakGradient_sharpCutoff n (physicalH1_weakGradient u))

@[simp] theorem physicalH1SharpCutoff_velocity (n : ℕ) (u : PhysicalH1) :
    physicalH1Velocity (physicalH1SharpCutoff n u) =
      sharpCutoff n (physicalH1Velocity u) := rfl

@[simp] theorem physicalH1SharpCutoff_gradient (n : ℕ) (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (physicalH1SharpCutoff n u) =
      sharpCutoff n (physicalH1Gradient j u) := rfl

private theorem physicalH1SharpCutoff_add (n : ℕ) (u v : PhysicalH1) :
    physicalH1SharpCutoff n (u + v) =
      physicalH1SharpCutoff n u + physicalH1SharpCutoff n v := by
  apply physicalH1Velocity_injective
  simp only [physicalH1SharpCutoff_velocity, map_add]

private theorem physicalH1SharpCutoff_smul (n : ℕ) (r : ℝ) (u : PhysicalH1) :
    physicalH1SharpCutoff n (r • u) = r • physicalH1SharpCutoff n u := by
  apply physicalH1Velocity_injective
  simp only [physicalH1SharpCutoff_velocity, map_smul]

theorem physicalH1SharpCutoff_norm_sq_le (n : ℕ) (u : PhysicalH1) :
    ‖physicalH1SharpCutoff n u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [physicalH1_norm_sq, physicalH1_norm_sq]
  simp only [physicalH1SharpCutoff_velocity, physicalH1SharpCutoff_gradient]
  apply add_le_add
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_sharpCutoff_le n _) 2
  · exact Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_sharpCutoff_le n _) 2)

theorem norm_physicalH1SharpCutoff_le (n : ℕ) (u : PhysicalH1) :
    ‖physicalH1SharpCutoff n u‖ ≤ ‖u‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (physicalH1SharpCutoff_norm_sq_le n u)

/-- The physical H1 lift is a contraction as a continuous real-linear map. -/
def physicalH1SharpCutoffCLM (n : ℕ) : PhysicalH1 →L[ℝ] PhysicalH1 :=
  ({ toFun := physicalH1SharpCutoff n
     map_add' := physicalH1SharpCutoff_add n
     map_smul' := physicalH1SharpCutoff_smul n } : PhysicalH1 →ₗ[ℝ] PhysicalH1).mkContinuous 1
    (fun u => by
      change ‖physicalH1SharpCutoff n u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_physicalH1SharpCutoff_le n u)

@[simp] theorem physicalH1SharpCutoffCLM_apply (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoffCLM n u = physicalH1SharpCutoff n u := rfl

theorem physicalH1SharpCutoff_idempotent (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoff n (physicalH1SharpCutoff n u) = physicalH1SharpCutoff n u := by
  apply physicalH1Velocity_injective
  simp only [physicalH1SharpCutoff_velocity, sharpCutoff_idempotent]

theorem inner_physicalH1SharpCutoff_left (n : ℕ) (u v : PhysicalH1) :
    inner ℝ (physicalH1SharpCutoff n u) v = inner ℝ u (physicalH1SharpCutoff n v) := by
  simp only [physicalH1_inner_eq, physicalH1SharpCutoff_velocity,
    physicalH1SharpCutoff_gradient, inner_sharpCutoff_left]

/-- The lifted cutoff and the existing lifted Leray projection commute exactly. -/
theorem physicalH1SharpCutoff_physicalH1Leray (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoff n (physicalH1Leray u) =
      physicalH1Leray (physicalH1SharpCutoff n u) := by
  apply physicalH1Velocity_injective
  simp only [physicalH1SharpCutoff_velocity, physicalH1Leray_velocity,
    sharpCutoff_realLeray]

end MethbokeAddon.R3Ehrenfest.SharpCutoff
