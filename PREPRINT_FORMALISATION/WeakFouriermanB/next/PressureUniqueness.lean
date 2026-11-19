import SingularClosure.PeriodicSobolev
import SingularClosure.CoordinateAverageOrthogonal
import SingularClosure.CriticalInitialPhysicalFourier
import SingularClosure.PeriodicFourierInjective
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Normalized physical pressure uniqueness on a velocity overlap

SOURCE_PREPARED_ONLY. External compilation and theorem-level audits pending.
This file is outside active Material discovery; no Lean ran locally.

The pressure SingularClosure.gradient, time derivative, convection, Laplacian and pressure
normalization are the literal operators/integrals from
`SingularClosure.Contracts`. The zero constant is derived from integration on
the actual unit cube. No pressure-equality, continuation or solution-existence
field is introduced.

Pinned API inspection: mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d,
`Analysis/Calculus/MeanValue.lean`: `is_const_of_fderiv_eq_zero`;
`Analysis/Calculus/Deriv/Basic.lean`:
`Filter.EventuallyEq.derivWithin_eq_of_nhds`.
The source-preserved foundation supplies `sum_coordinate_unitVector` and
`integral_unitCube_productMeasure`, including the proved probability-measure
instance on the product of three unit intervals.

Scope: equality of pressure is proved from equality of the actual velocity on
an open time set, the two actual NSE equations, smooth pressure slices and
literal zero-mean normalization. Obtaining the velocity overlap and gluing the
full solution remain separate obligations; this file does not complete WFB-09.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB
open SingularClosure
noncomputable section

/-- Actual continuous periodic velocity fields agreeing almost everywhere on
the fundamental cube agree pointwise everywhere. This uses equality of their
literal Fourier integrals and the existing physical Fourier injectivity theorem.
-/
theorem continuous_periodic_field_eq_of_cube_ae
    {u v : Field} (hu : Continuous u) (hv : Continuous v)
    (huper : SpatialPeriodic u) (hvper : SpatialPeriodic v)
    (hae : u =ᵐ[volume.restrict unitCube] v) : u = v := by
  exact datumFourierCoeff_injective_continuous_periodic u v hu hv huper hvper
    (criticalCube_datumFourierCoeff_congr_ae hae)

/-- Integrating a scalar constant over the actual Euclidean fundamental cube
returns the constant, using the proved unit-volume product representation. -/
theorem pressure_integral_unitCube_const (c : ℝ) :
    (∫ _x : Vec in unitCube, c) = c := by
  rw [integral_unitCube_productMeasure]
  simp

/-- The actual scalar SingularClosure.gradient records every coordinate of the Fréchet
derivative. Equality of these gradients therefore determines the whole map. -/
theorem scalar_fderiv_eq_of_gradient_eq
    {p q : Vec → ℝ} {x : Vec} (hgrad : SingularClosure.gradient p x = SingularClosure.gradient q x) :
    fderiv ℝ p x = fderiv ℝ q x := by
  have hcoord (i : Fin 3) :
      fderiv ℝ p x (unitVector i) = fderiv ℝ q x (unitVector i) := by
    have h := congrArg (fun v : Vec => v i) hgrad
    change fderiv ℝ p x (unitVector i) = fderiv ℝ q x (unitVector i) at h
    exact h
  apply ContinuousLinearMap.ext
  intro y
  have hrepr (L : Vec →L[ℝ] ℝ) :
      L y = ∑ i : Fin 3, y i • L (unitVector i) := by
    have h := congrArg L (sum_coordinate_unitVector y)
    simpa only [map_sum, map_smul] using h.symm
  rw [hrepr (fderiv ℝ p x), hrepr (fderiv ℝ q x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoord i]

/-- Smooth physical pressures with the same SingularClosure.gradient differ by a constant;
their actual zero spatial means force that constant to vanish. -/
theorem normalized_pressure_eq_of_gradient_eq
    {p q : Vec → ℝ}
    (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hpmean : PressureMeanZero p) (hqmean : PressureMeanZero q)
    (hgrad : ∀ x : Vec, SingularClosure.gradient p x = SingularClosure.gradient q x) : p = q := by
  have hpD : Differentiable ℝ p := hp.differentiable (by simp)
  have hqD : Differentiable ℝ q := hq.differentiable (by simp)
  have hzero (x : Vec) : fderiv ℝ (fun y : Vec => p y - q y) x = 0 := by
    change fderiv ℝ (p - q) x = 0
    rw [fderiv_sub (hpD x) (hqD x),
      scalar_fderiv_eq_of_gradient_eq (hgrad x), sub_self]
  have hconstant : (fun x : Vec => p x - q x) =
      (fun _ : Vec => p 0 - q 0) := by
    funext x
    exact is_const_of_fderiv_eq_zero (hpD.sub hqD) hzero x 0
  have hc : p 0 - q 0 = 0 := by
    calc
      p 0 - q 0 = ∫ x in unitCube, p x - q x := by
        rw [hconstant, pressure_integral_unitCube_const]
      _ = 0 := by
        rw [integral_sub hpmean.1 hqmean.1, hpmean.2, hqmean.2, sub_self]
  funext x
  exact sub_eq_zero.mp ((congrFun hconstant x).trans hc)

/-- Pointwise velocity agreement on an open time neighborhood gives equality
of the literal right-half-line time derivatives, including the operator's
boundary convention. No replacement derivative is assumed. -/
theorem timeDerivative_eq_on_open_velocity_overlap
    {u v : Velocity} {I : Set ℝ} (hI : IsOpen I)
    (hvel : ∀ t ∈ I, u t = v t) {t : ℝ} (ht : t ∈ I) (x : Vec) :
    timeDerivative u t x = timeDerivative v t x := by
  have hevent : (fun s : ℝ => u s x) =ᶠ[𝓝 t] (fun s : ℝ => v s x) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact congrFun (hvel s hs) x
  exact hevent.derivWithin_eq_of_nhds

/-- On an open velocity overlap, the two literal NSE equations have identical
time, convection and viscosity terms, hence identical pressure gradients. -/
theorem pressure_gradient_eq_on_open_velocity_overlap
    {ν : ℝ} {u v : Velocity} {p q : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hvel : ∀ t ∈ I, u t = v t)
    (hu : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (u t) x)
    (hv : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
        ν • laplacian (v t) x) :
    ∀ t ∈ I, SingularClosure.gradient (p t) = SingularClosure.gradient (q t) := by
  intro t ht
  funext x
  have htime := timeDerivative_eq_on_open_velocity_overlap hI hvel ht x
  have hleft := hu t ht x
  rw [htime, hvel t ht] at hleft
  exact add_left_cancel (hleft.trans (hv t ht x).symm)

/-- The pressure part of same-path gluing is forced, once the actual velocity
overlap, equations, smooth pressure slices and zero means have been proved. -/
theorem normalized_pressure_eq_on_open_velocity_overlap
    {ν : ℝ} {u v : Velocity} {p q : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hvel : ∀ t ∈ I, u t = v t)
    (hu : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (u t) x)
    (hv : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
        ν • laplacian (v t) x)
    (hp : ∀ t ∈ I, ContDiff ℝ ∞ (p t))
    (hq : ∀ t ∈ I, ContDiff ℝ ∞ (q t))
    (hpmean : ∀ t ∈ I, PressureMeanZero (p t))
    (hqmean : ∀ t ∈ I, PressureMeanZero (q t)) :
    ∀ t ∈ I, p t = q t := by
  intro t ht
  exact normalized_pressure_eq_of_gradient_eq (hp t ht) (hq t ht)
    (hpmean t ht) (hqmean t ht)
    (fun x => congrFun
      (pressure_gradient_eq_on_open_velocity_overlap hI hvel hu hv t ht) x)

/-- Joint smoothness on an open time cylinder supplies each smooth pressure
slice by composition with the fixed-time inclusion. -/
theorem pressure_slice_contDiff_on_open_time_set
    {p : Pressure} {I : Set ℝ} (hI : IsOpen I)
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I}) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (p t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hopen : IsOpen {z : ℝ × Vec | z.1 ∈ I} := hI.preimage continuous_fst
  have hj := hp.contDiffAt (hopen.mem_nhds
    (show (t, x) ∈ {z : ℝ × Vec | z.1 ∈ I} from ht))
  simpa only [Function.comp_def] using
    hj.comp x (contDiff_prodMk_right t).contDiffAt

/-- Jointly smooth normalized pressures agree pointwise throughout an open
time interval wherever their actual NSE velocities already agree there. -/
theorem normalized_pressure_eq_on_jointly_smooth_velocity_overlap
    {ν : ℝ} {u v : Velocity} {p q : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hvel : ∀ t ∈ I, u t = v t)
    (hu : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (u t) x)
    (hv : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
        ν • laplacian (v t) x)
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I})
    (hq : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => q z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I})
    (hpmean : ∀ t ∈ I, PressureMeanZero (p t))
    (hqmean : ∀ t ∈ I, PressureMeanZero (q t)) :
    ∀ t ∈ I, p t = q t := by
  exact normalized_pressure_eq_on_open_velocity_overlap hI hvel hu hv
    (fun _ ht => pressure_slice_contDiff_on_open_time_set hI hp ht)
    (fun _ ht => pressure_slice_contDiff_on_open_time_set hI hq ht)
    hpmean hqmean

end
end MethbokeAddon.WeakFouriermanB
