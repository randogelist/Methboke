import SingularClosure.CriticalWeakMomentum

/-!
Finite-window version of the actual physical weak/classical cross identity.

The velocity used for testing is globally a positive-time smooth solenoidal
test, as required by the existing weak momentum definition. It is required to
solve NSE only on the selected compact interval [s,t]. A smooth finite-front
time clamp can supply such a test without extending the NSE solution globally.

This is prepared source, not externally compiled evidence. It is outside active
Material discovery. No local Lean execution is permitted or has been performed.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Interval Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

private theorem window_inner_sub_right (v f g : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hf : Continuous f)
    (hg : Continuous g) :
    physicalFieldInner v (f - g) = physicalFieldInner v f - physicalFieldInner v g := by
  unfold physicalFieldInner
  simp_rw [Pi.sub_apply, inner_sub_right]
  exact integral_sub (criticalWeakFieldInner_integrable v f hv hf)
    (criticalWeakFieldInner_integrable v g hv hg)

private theorem window_inner_smul_right (v f : Field) (c : ℝ) :
    physicalFieldInner v (c • f) = c * physicalFieldInner v f := by
  unfold physicalFieldInner
  simp only [Pi.smul_apply, inner_smul_right]
  exact integral_const_mul _ _

/-- The physical cross identity only needs the classical equation and pressure
regularity on the interval of integration. No global classical evolution, weak
gradient of v, relative-energy inequality, or comparison conclusion is assumed.
-/
theorem finite_window_weak_classical_cross_identity
    (ν : ℝ) (v φ : Velocity) (p : Pressure)
    (hv : CriticalIntegratedWeakMomentum ν v)
    (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative φ r x + convection (φ r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (φ r) x) :
    IntervalIntegrable (fun r =>
      2 * ν * physicalFieldInner (v r) (laplacian (φ r)) -
        physicalFieldInner (v r) (convection (φ r)) + criticalWeakTransport (v r) (φ r))
      volume s t ∧
    physicalFieldInner (v t) (φ t) - physicalFieldInner (v s) (φ s) =
      ∫ r in s..t,
        2 * ν * physicalFieldInner (v r) (laplacian (φ r)) -
          physicalFieldInner (v r) (convection (φ r)) + criticalWeakTransport (v r) (φ r) := by
  have hpoint (r : ℝ) (hr : r ∈ Icc s t) :
      criticalWeakMomentumIntegrand ν v φ r =
        2 * ν * physicalFieldInner (v r) (laplacian (φ r)) -
          physicalFieldInner (v r) (convection (φ r)) + criticalWeakTransport (v r) (φ r) := by
    have hrpos : 0 < r := hs.trans_le hr.1
    have hφs := hφ.spatial_smooth hrpos
    have hlap : Continuous (laplacian (φ r)) := (laplacian_contDiff (φ r) hφs).continuous
    have hconv : Continuous (convection (φ r)) := convection_continuous hφs
    have hgrad : Continuous (SingularClosure.gradient (p r)) := criticalWeak_gradient_continuous _ (hp r hr)
    have htime : timeDerivative φ r = ν • laplacian (φ r) - convection (φ r) - SingularClosure.gradient (p r) := by
      funext x
      change timeDerivative φ r x =
        ν • laplacian (φ r) x - convection (φ r) x - SingularClosure.gradient (p r) x
      calc
        _ = (timeDerivative φ r x + convection (φ r) x + SingularClosure.gradient (p r) x) -
            convection (φ r) x - SingularClosure.gradient (p r) x := by abel
        _ = _ := by rw [hNSE r hr x]
    have hνlap : Continuous (ν • laplacian (φ r)) := continuous_const.smul hlap
    have hpair : physicalFieldInner (v r) (timeDerivative φ r) =
        ν * physicalFieldInner (v r) (laplacian (φ r)) -
          physicalFieldInner (v r) (convection (φ r)) := by
      rw [htime,
        window_inner_sub_right _ _ _ (hv.spatial_L2 r hrpos) (hνlap.sub hconv) hgrad,
        window_inner_sub_right _ _ _ (hv.spatial_L2 r hrpos) hνlap hconv,
        window_inner_smul_right,
        hv.gradient_annihilation r hrpos (p r) (hp r hr) (hpp r hr), sub_zero]
    unfold criticalWeakMomentumIntegrand
    rw [hpair]
    ring
  obtain ⟨hI₁, hI₂, hI₃⟩ := hv.test_integrable φ hφ s t hs hst
  have hI : IntervalIntegrable (criticalWeakMomentumIntegrand ν v φ) volume s t :=
    (hI₁.add (hI₂.const_mul ν)).add hI₃
  refine ⟨?_, ?_⟩
  · apply hI.congr
    intro r hr
    have hr' : r ∈ Ioc s t := by simpa only [uIoc_of_le hst] using hr
    exact hpoint r ⟨hr'.1.le, hr'.2⟩
  · apply (hv.momentum φ hφ s t hs hst).trans
    apply intervalIntegral.integral_congr
    intro r hr
    exact hpoint r (by simpa only [uIcc_of_le hst] using hr)

end

end MethbokeAddon.WeakFouriermanB
