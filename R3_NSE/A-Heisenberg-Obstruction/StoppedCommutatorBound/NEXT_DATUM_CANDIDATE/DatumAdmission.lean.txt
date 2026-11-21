import MethbokeAddon.R3Ehrenfest.Contracts
import MethbokeAddon.QuasiFeffermanA.PhysicalH2
import MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence

/-!
# Literal Schwartz datum admission into the physical whole-space carriers

A literal `R3Ehrenfest.SmoothDatum` already contains an actual real Schwartz
field and pointwise classical divergence zero.  This file turns those data into
the native full-volume `EnergyDatum`, `PhysicalH1Sigma`, `PhysicalH2`, and
`PhysicalH2Sigma` objects used by the whole-space cutoff construction.

The only analytic step is the exact bridge from pointwise Schwartz divergence
to the compact-test `Solenoidal` predicate.  It is proved through the accepted
physical weak-gradient trace theorem, using the genuine Schwartz derivative
representatives in `L2`.

This package constructs initial-data objects only.  It does not construct the
nonlinear cutoff flow, a stopped-bound witness, a literal NSE-A solution, or the
R3 obstruction root.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff LineDeriv

namespace MethbokeAddon.R3Ehrenfest.DatumAdmission

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence

/-- The literal pointwise divergence field is exactly the sum of the three
Schwartz coordinate derivatives used by the native physical graph. -/
theorem smoothDatum_divergence_sum (a : SmoothDatum) (x : Space) :
    (∑ j : Fin 3,
      (fderiv ℝ (a.value : Space → Space) x (coordinateVector j)) j) = 0 := by
  simpa only [SingularClosure.divergence, SingularClosure.coordinateDerivative,
    SingularClosure.unitVector, coordinateVector] using a.divergence_free x

/-- The actual `L2` trace of the Schwartz gradient vanishes. -/
theorem smoothDatum_spatialGradientTrace_eq_zero (a : SmoothDatum) :
    spatialGradientTrace
      (fun j : Fin 3 => (∂_{coordinateVector j} a.value).toLp 2 volume) = 0 := by
  apply Lp.ext
  have hderiv : ∀ᵐ x : Space ∂volume, ∀ j : Fin 3,
      ((∂_{coordinateVector j} a.value).toLp 2 volume : SpatialL2) x =
        (∂_{coordinateVector j} a.value) x := by
    exact ae_all_iff.mpr fun j =>
      (∂_{coordinateVector j} a.value).coeFn_toLp 2 volume
  filter_upwards [spatialGradientTrace_ae
      (fun j : Fin 3 => (∂_{coordinateVector j} a.value).toLp 2 volume),
    hderiv] with x htrace hx
  rw [htrace]
  simp_rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [smoothDatum_divergence_sum a x]
  simp

/-- Pointwise divergence-free Schwartz data satisfy the actual full-volume
compact-test solenoidal predicate. -/
theorem smoothDatum_solenoidal (a : SmoothDatum) :
    Solenoidal (a.value.toLp 2 volume) := by
  exact (spatialWeakGradient_solenoidal_iff_trace_eq_zero
    (schwartz_spatialWeakGradient a.value)).2
      (smoothDatum_spatialGradientTrace_eq_zero a)

/-- Literal smooth data as actual finite-energy solenoidal data. -/
def smoothDatumToEnergyDatum (a : SmoothDatum) : EnergyDatum :=
  ⟨a.value.toLp 2 volume, smoothDatum_solenoidal a⟩

@[simp] theorem smoothDatumToEnergyDatum_val (a : SmoothDatum) :
    (smoothDatumToEnergyDatum a).val = a.value.toLp 2 volume := rfl

/-- Literal smooth data in the complete physical `H1_sigma` carrier. -/
def smoothDatumToPhysicalH1Sigma (a : SmoothDatum) : PhysicalH1Sigma :=
  schwartzToPhysicalH1Sigma a.value (smoothDatum_solenoidal a)

@[simp] theorem smoothDatumToPhysicalH1Sigma_velocity (a : SmoothDatum) :
    (smoothDatumToPhysicalH1Sigma a).val 0 = a.value.toLp 2 volume := rfl

/-- Literal smooth data in the actual thirteen-component physical `H2` graph. -/
def smoothDatumToPhysicalH2 (a : SmoothDatum) : PhysicalH2 :=
  schwartzToPhysicalH2 a.value

@[simp] theorem smoothDatumToPhysicalH2_velocity (a : SmoothDatum) :
    physicalH2Velocity (smoothDatumToPhysicalH2 a) =
      a.value.toLp 2 volume := rfl

@[simp] theorem smoothDatumToPhysicalH2_gradient (a : SmoothDatum) (j : Fin 3) :
    physicalH2Gradient j (smoothDatumToPhysicalH2 a) =
      (∂_{coordinateVector j} a.value).toLp 2 volume := rfl

@[simp] theorem smoothDatumToPhysicalH2_hessian
    (a : SmoothDatum) (j k : Fin 3) :
    physicalH2Hessian j k (smoothDatumToPhysicalH2 a) =
      (∂_{coordinateVector k} (∂_{coordinateVector j} a.value)).toLp 2 volume := rfl

/-- Literal smooth data in the complete solenoidal physical `H2` carrier. -/
def smoothDatumToPhysicalH2Sigma (a : SmoothDatum) : PhysicalH2Sigma := by
  refine ⟨(smoothDatumToPhysicalH2 a).val, ?_⟩
  apply (mem_physicalH2SigmaGraph_iff _).mpr
  exact ⟨(mem_physicalH2Graph_iff _).mp (smoothDatumToPhysicalH2 a).property,
    smoothDatum_solenoidal a⟩

/-- Forgetting the solenoidal subtype returns the same constructed physical
`H2` datum, not merely one with the same velocity. -/
theorem smoothDatumToPhysicalH2Sigma_toH2 (a : SmoothDatum) :
    physicalH2SigmaToH2LI (smoothDatumToPhysicalH2Sigma a) =
      smoothDatumToPhysicalH2 a := by
  apply Subtype.ext
  rfl

@[simp] theorem smoothDatumToPhysicalH2Sigma_velocity (a : SmoothDatum) :
    physicalH2Velocity
        (physicalH2SigmaToH2LI (smoothDatumToPhysicalH2Sigma a)) =
      a.value.toLp 2 volume := by
  rw [smoothDatumToPhysicalH2Sigma_toH2]
  exact smoothDatumToPhysicalH2_velocity a

/-- The constructed `H2_sigma` datum retains the actual compact-test
solenoidal condition. -/
theorem smoothDatumToPhysicalH2Sigma_solenoidal (a : SmoothDatum) :
    Solenoidal
      (physicalH2Velocity
        (physicalH2SigmaToH2LI (smoothDatumToPhysicalH2Sigma a))) :=
  physicalH2Sigma_solenoidal (smoothDatumToPhysicalH2Sigma a)

end MethbokeAddon.R3Ehrenfest.DatumAdmission
