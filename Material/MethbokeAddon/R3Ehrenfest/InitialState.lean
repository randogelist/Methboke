import MethbokeAddon.R3Ehrenfest.DatumAdmission
import MethbokeAddon.R3Ehrenfest.Carrier
import MethbokeAddon.R3Ehrenfest.Bandlimited

/-!
# Canonical carrier-valued initial state for the R3 cutoff evolution

For a literal divergence-free Schwartz datum `a`, this file constructs the
actual carrier element `J_n a` used as the initial condition of the whole-space
regularized evolution. It records the exact cutoff and Leray fixed-point laws,
solenoidality and L2 norm control, together with the already constructed
physical H2 and H2-sigma lifts of the same initial state.

No trajectory, nonlinear vector field, local existence, energy identity,
stopped-bound witness or R3 obstruction root is asserted here.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory

namespace MethbokeAddon.R3Ehrenfest.InitialState

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.LeraySolenoidal
open MethbokeAddon.R3Ehrenfest.DatumAdmission
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.Carrier
open MethbokeAddon.R3Ehrenfest.Bandlimited

/-- The canonical carrier-valued cutoff of a literal Schwartz datum. -/
def smoothDatumInitialState (n : ℕ) (a : SmoothDatum) :
    BandlimitedSolenoidal n :=
  bandlimitedProject n (a.value.toLp 2 volume)

@[simp] theorem smoothDatumInitialState_coe (n : ℕ) (a : SmoothDatum) :
    ((smoothDatumInitialState n a : BandlimitedSolenoidal n) : SpatialL2) =
      sharpCutoff n (a.value.toLp 2 volume) := by
  rw [smoothDatumInitialState, bandlimitedProject_coe]
  rw [(realLeray_eq_self_iff_solenoidal _).2 (smoothDatum_solenoidal a)]

/-- The initial state lies literally in the cutoff fixed-point range. -/
theorem smoothDatumInitialState_cutoff_fixed (n : ℕ) (a : SmoothDatum) :
    sharpCutoff n (smoothDatumInitialState n a : SpatialL2) =
      (smoothDatumInitialState n a : SpatialL2) :=
  sharpCutoff_coe n (smoothDatumInitialState n a)

/-- The initial state lies literally in the Leray fixed-point range. -/
theorem smoothDatumInitialState_leray_fixed (n : ℕ) (a : SmoothDatum) :
    realLeray (smoothDatumInitialState n a : SpatialL2) =
      (smoothDatumInitialState n a : SpatialL2) :=
  realLeray_coe n (smoothDatumInitialState n a)

/-- The actual compact-test solenoidal predicate is retained. -/
theorem smoothDatumInitialState_solenoidal (n : ℕ) (a : SmoothDatum) :
    Solenoidal (smoothDatumInitialState n a : SpatialL2) :=
  solenoidal_coe n (smoothDatumInitialState n a)

/-- The projection does not increase the actual L2 norm. -/
theorem norm_smoothDatumInitialState_le (n : ℕ) (a : SmoothDatum) :
    ‖smoothDatumInitialState n a‖ ≤ ‖a.value.toLp 2 volume‖ := by
  simpa only [smoothDatumInitialState] using
    norm_bandlimitedProject_le n (a.value.toLp 2 volume)

/-- The physical H2 lift of exactly the same sharp-cutoff datum. -/
def smoothDatumInitialH2 (n : ℕ) (a : SmoothDatum) : PhysicalH2 :=
  sharpCutoffH2 n (a.value.toLp 2 volume)

@[simp] theorem smoothDatumInitialH2_velocity (n : ℕ) (a : SmoothDatum) :
    physicalH2Velocity (smoothDatumInitialH2 n a) =
      sharpCutoff n (a.value.toLp 2 volume) := rfl

@[simp] theorem smoothDatumInitialH2_gradient
    (n : ℕ) (a : SmoothDatum) (j : Fin 3) :
    physicalH2Gradient j (smoothDatumInitialH2 n a) =
      cutoffDerivative n j (a.value.toLp 2 volume) := rfl

@[simp] theorem smoothDatumInitialH2_hessian
    (n : ℕ) (a : SmoothDatum) (j k : Fin 3) :
    physicalH2Hessian j k (smoothDatumInitialH2 n a) =
      cutoffDerivative n k (cutoffDerivative n j (a.value.toLp 2 volume)) := rfl

/-- The H2 lift and the carrier-valued initial state have exactly the same
actual velocity. -/
theorem smoothDatumInitialH2_velocity_eq_state (n : ℕ) (a : SmoothDatum) :
    physicalH2Velocity (smoothDatumInitialH2 n a) =
      (smoothDatumInitialState n a : SpatialL2) := by
  rw [smoothDatumInitialH2_velocity, smoothDatumInitialState_coe]

/-- Explicit fixed-cutoff H2 norm control. -/
theorem norm_smoothDatumInitialH2_le (n : ℕ) (a : SmoothDatum) :
    ‖smoothDatumInitialH2 n a‖ ≤
      sharpCutoffH2Bound n * ‖a.value.toLp 2 volume‖ :=
  norm_sharpCutoffH2_le n (a.value.toLp 2 volume)

/-- The same initial state in the complete physical H2-sigma carrier. -/
def smoothDatumInitialH2Sigma (n : ℕ) (a : SmoothDatum) : PhysicalH2Sigma := by
  refine ⟨(smoothDatumInitialH2 n a).val, ?_⟩
  apply (mem_physicalH2SigmaGraph_iff _).mpr
  refine ⟨(mem_physicalH2Graph_iff _).mp (smoothDatumInitialH2 n a).property, ?_⟩
  change Solenoidal (physicalH2Velocity (smoothDatumInitialH2 n a))
  rw [smoothDatumInitialH2_velocity_eq_state]
  exact smoothDatumInitialState_solenoidal n a

/-- Forgetting the H2-sigma subtype returns the exact constructed H2 lift. -/
theorem smoothDatumInitialH2Sigma_toH2 (n : ℕ) (a : SmoothDatum) :
    physicalH2SigmaToH2LI (smoothDatumInitialH2Sigma n a) =
      smoothDatumInitialH2 n a := by
  apply Subtype.ext
  rfl

@[simp] theorem smoothDatumInitialH2Sigma_velocity (n : ℕ) (a : SmoothDatum) :
    physicalH2Velocity
        (physicalH2SigmaToH2LI (smoothDatumInitialH2Sigma n a)) =
      (smoothDatumInitialState n a : SpatialL2) := by
  rw [smoothDatumInitialH2Sigma_toH2]
  exact smoothDatumInitialH2_velocity_eq_state n a

/-- The projected initial state is recovered by the actual carrier projection. -/
theorem smoothDatumInitialState_projected (n : ℕ) (a : SmoothDatum) :
    bandlimitedProject n (smoothDatumInitialState n a : SpatialL2) =
      smoothDatumInitialState n a :=
  bandlimitedProject_inclusion n (smoothDatumInitialState n a)

end MethbokeAddon.R3Ehrenfest.InitialState
