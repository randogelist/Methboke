import MethbokeAddon.R3Ehrenfest.SharpCutoff

/-!
# The actual closed bandlimited solenoidal L2 carrier

The state space is the intersection of the fixed-point spaces of the actual
sharp cutoff and whole-space Leray projection. It is a closed subspace of the
existing real L2 Hilbert space, hence complete. The constructed map onto it
is exactly the composition of those two commuting orthogonal projections.

No finite-dimensionality, compactness of bounded balls, local flow, or PDE
existence is assumed or concluded. New derivative and nonlinear estimates
on this carrier remain separate analytical steps.

Prepared source requires matching authorized external cached verification.
No local Lean, Lake, kernel audit or proof runner is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace MethbokeAddon.R3Ehrenfest.Carrier

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.LerayMultiplier
open MethbokeAddon.QuasiFeffermanA.LeraySolenoidal
open QFA.Endpoints.Agmon (ComplexL2)
open QFA.Endpoints.Representation
open SharpCutoff

/-- The closed intersection of the two actual fixed-point kernels. -/
def bandlimitedSolenoidalGraph (n : ℕ) : ClosedSubmodule ℝ SpatialL2 :=
  (⟨(sharpCutoff n - ContinuousLinearMap.id ℝ SpatialL2).ker,
      (sharpCutoff n - ContinuousLinearMap.id ℝ SpatialL2).isClosed_ker⟩ :
    ClosedSubmodule ℝ SpatialL2) ⊓
  (⟨(realLerayCLM - ContinuousLinearMap.id ℝ SpatialL2).ker,
      (realLerayCLM - ContinuousLinearMap.id ℝ SpatialL2).isClosed_ker⟩ :
    ClosedSubmodule ℝ SpatialL2)

theorem mem_bandlimitedSolenoidalGraph_iff (n : ℕ) (v : SpatialL2) :
    v ∈ bandlimitedSolenoidalGraph n ↔ sharpCutoff n v = v ∧ realLeray v = v := by
  change (sharpCutoff n v - v = 0 ∧ realLeray v - v = 0) ↔ _
  simp only [sub_eq_zero]

/-- The inherited real Hilbert carrier; it is not a finite-dimensional surrogate. -/
abbrev BandlimitedSolenoidal (n : ℕ) := (bandlimitedSolenoidalGraph n).toSubmodule

instance bandlimitedSolenoidalCompleteSpace (n : ℕ) :
    CompleteSpace (BandlimitedSolenoidal n) :=
  (bandlimitedSolenoidalGraph n).isClosed.isComplete.completeSpace_coe

theorem bandlimitedSolenoidal_isClosed (n : ℕ) :
    IsClosed (bandlimitedSolenoidalGraph n : Set SpatialL2) :=
  (bandlimitedSolenoidalGraph n).isClosed

/-- The original L2 inclusion, as a bounded real-linear map. -/
def bandlimitedInclusionCLM (n : ℕ) : BandlimitedSolenoidal n →L[ℝ] SpatialL2 :=
  (bandlimitedSolenoidalGraph n).toSubmodule.subtypeL

@[simp] theorem bandlimitedInclusionCLM_apply (n : ℕ) (v : BandlimitedSolenoidal n) :
    bandlimitedInclusionCLM n v = (v : SpatialL2) := rfl

theorem sharpCutoff_coe (n : ℕ) (v : BandlimitedSolenoidal n) :
    sharpCutoff n (v : SpatialL2) = (v : SpatialL2) :=
  ((mem_bandlimitedSolenoidalGraph_iff n v).mp v.property).1

theorem realLeray_coe (n : ℕ) (v : BandlimitedSolenoidal n) :
    realLeray (v : SpatialL2) = (v : SpatialL2) :=
  ((mem_bandlimitedSolenoidalGraph_iff n v).mp v.property).2

theorem solenoidal_coe (n : ℕ) (v : BandlimitedSolenoidal n) :
    Solenoidal (v : SpatialL2) :=
  (realLeray_eq_self_iff_solenoidal v).mp (realLeray_coe n v)

/-- The actual composed projection lands in the stated carrier. -/
theorem sharpCutoff_realLeray_mem (n : ℕ) (v : SpatialL2) :
    sharpCutoff n (realLeray v) ∈ bandlimitedSolenoidalGraph n := by
  apply (mem_bandlimitedSolenoidalGraph_iff n _).mpr
  constructor
  · exact sharpCutoff_idempotent n (realLeray v)
  · rw [← sharpCutoff_realLeray, realLeray_idempotent]

/-- Projection onto the actual closed bandlimited solenoidal space. -/
def bandlimitedProject (n : ℕ) : SpatialL2 →L[ℝ] BandlimitedSolenoidal n :=
  ({ toFun := fun v => ⟨(sharpCutoff n).comp realLerayCLM v,
        sharpCutoff_realLeray_mem n v⟩
     map_add' := by
       intro u v
       apply Subtype.ext
       exact map_add ((sharpCutoff n).comp realLerayCLM) u v
     map_smul' := by
       intro r v
       apply Subtype.ext
       exact map_smul ((sharpCutoff n).comp realLerayCLM) r v } :
    SpatialL2 →ₗ[ℝ] BandlimitedSolenoidal n).mkContinuous 1
      (fun v => by
        change ‖sharpCutoff n (realLeray v)‖ ≤ 1 * ‖v‖
        simpa only [one_mul] using
          (norm_sharpCutoff_le n (realLeray v)).trans (norm_realLeray_le v))

@[simp] theorem bandlimitedProject_coe (n : ℕ) (v : SpatialL2) :
    (bandlimitedProject n v : SpatialL2) = sharpCutoff n (realLeray v) := rfl

theorem norm_bandlimitedProject_le (n : ℕ) (v : SpatialL2) :
    ‖bandlimitedProject n v‖ ≤ ‖v‖ :=
  (norm_sharpCutoff_le n (realLeray v)).trans (norm_realLeray_le v)

/-- Every element is recovered exactly after its original L2 inclusion. -/
theorem bandlimitedProject_inclusion (n : ℕ) (v : BandlimitedSolenoidal n) :
    bandlimitedProject n (v : SpatialL2) = v := by
  apply Subtype.ext
  rw [bandlimitedProject_coe, realLeray_coe, sharpCutoff_coe]

theorem bandlimitedProject_surjective (n : ℕ) : Function.Surjective (bandlimitedProject n) := by
  intro v
  exact ⟨(v : SpatialL2), bandlimitedProject_inclusion n v⟩

/-- The composed projection remains self-adjoint in the ambient L2 inner product. -/
theorem inner_bandlimitedProject_left (n : ℕ) (u v : SpatialL2) :
    inner ℝ (bandlimitedProject n u : SpatialL2) v =
      inner ℝ u (bandlimitedProject n v : SpatialL2) := by
  rw [bandlimitedProject_coe, bandlimitedProject_coe, inner_sharpCutoff_left,
    inner_realLeray_left, ← sharpCutoff_realLeray]

/-- Every carrier element has the promised literal Fourier support. -/
theorem bandlimitedSolenoidal_fourier_outside (n : ℕ) (v : BandlimitedSolenoidal n) :
    ∀ᵐ ξ : Space ∂volume, cutoffRadius n < ‖ξ‖ →
      (𝓕 (complexifyL2 (v : SpatialL2)) : ComplexL2) ξ = 0 := by
  simpa only [sharpCutoff_coe] using sharpCutoff_fourier_outside n (v : SpatialL2)

end MethbokeAddon.R3Ehrenfest.Carrier
