import MethbokeAddon.WeakFouriermanB.SmoothDatum
import MethbokeAddon.WeakFouriermanB.FiniteFrontTest
import MethbokeAddon.WeakFouriermanB.FiniteWindowSerrinComparison

/-!
Identify an actual finite physical NSE front with an original Leray--Hopf path.

The global smooth object used in weak momentum is an explicitly constructed
test. Only the original finite front solves NSE; no strong local existence,
continuation, maximal trajectory, or global smooth conclusion is assumed.
The initial LH datum is the literal physical L2 representative of the same a.

Prepared source only. External cached compiler/type/axiom evidence is pending.
No local Lean execution; staged outside active Material discovery.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- Finite-window physical comparison for the same initial datum. The Serrin
condition is the actual norm of the original velocity on the shorter interval.
-/
theorem local_front_leray_hopf_identification_on
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (τ : ℝ) (hτ0 : 0 < τ) (hτT : τ < T)
    (hSerrin : MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ))) :
    ∀ r ∈ Ioc (0 : ℝ) τ, v r =ᵐ[volume.restrict unitCube] u r := by
  obtain ⟨φ, hφ, hagree, hzero⟩ :=
    local_front_exists_global_test_through ν T a u p H τ hτ0 hτT
  have hfront : Ioc (0 : ℝ) τ ⊆ Ioo (0 : ℝ) T :=
    fun r hr => ⟨hr.1, hr.2.trans_lt hτT⟩
  have hvalue (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) τ) : φ r = u r :=
    (hagree r hr).self_of_nhds
  have hpressure : ∀ r ∈ Ioc (0 : ℝ) τ, ContDiff ℝ ∞ (p r) :=
    fun r hr => local_front_pressure_slice_smooth ν T a u p H r (hfront hr)
  have hpressurePeriodic : ∀ r ∈ Ioc (0 : ℝ) τ, SpatialPeriodic (p r) :=
    fun r hr => H.pressure_periodic r (hfront hr)
  have hequation : ∀ r ∈ Ioc (0 : ℝ) τ, ∀ x : Vec,
      timeDerivative φ r x + convection (φ r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (φ r) x := by
    intro r hr x
    rw [local_test_timeDerivative_eq_of_eventuallyEq (hagree r hr) x, hvalue r hr]
    exact H.equation r (hfront hr) x
  have htrace : Tendsto
      (fun r => eLpNorm (φ r - (criticalL2Representative a : Field))
        2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply H.strong_initial_trace.congr'
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds] with r hr
    rw [hr]
    apply eLpNorm_congr_ae
    exact Filter.EventuallyEq.sub Filter.EventuallyEq.rfl
      (smooth_datum_representative_ae H.initial_smooth).symm
  have hnorm : (fun r => criticalSpatialNorm 6 (u r)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) τ)] (fun r => criticalSpatialNorm 6 (φ r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [hvalue r hr]
  have hφSerrin : MemLp (fun r => criticalSpatialNorm 6 (φ r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ)) :=
    (memLp_congr_ae hnorm).mp hSerrin
  have hcomparison := finite_window_leray_hopf_serrin_comparison
    ν H.viscosity_pos (criticalL2Representative a) v φ G p hv hφ τ hτ0
    hpressure hpressurePeriodic hequation htrace hφSerrin
  intro r hr
  simpa only [hvalue r hr] using hcomparison r hr

/-- Bounds on every shorter interval suffice; no integrability through the
open cap itself is required. This is the form used by an admitted analytic cap.
-/
theorem local_front_leray_hopf_identification_of_compact_serrin
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hSerrin : ∀ τ : ℝ, 0 < τ → τ < T →
      MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
        (volume.restrict (Ioc (0 : ℝ) τ))) :
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r := by
  intro r hr
  exact local_front_leray_hopf_identification_on ν T a u p v G H hv r hr.1 hr.2
    (hSerrin r hr.1 hr.2) r ⟨hr.1, le_rfl⟩

/-- A finite actual Serrin norm on the open front identifies every strictly
pre-endpoint slice with the same original weak path.
-/
theorem local_front_leray_hopf_identification_of_serrin
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hSerrin : MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioo (0 : ℝ) T))) :
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r := by
  intro r hr
  have hsubset : Ioc (0 : ℝ) r ⊆ Ioo (0 : ℝ) T :=
    fun q hq => ⟨hq.1, hq.2.trans_lt hr.2⟩
  have hlocal := hSerrin.mono_measure (Measure.restrict_mono_set volume hsubset)
  exact local_front_leray_hopf_identification_on ν T a u p v G H hv r hr.1 hr.2
    hlocal r ⟨hr.1, le_rfl⟩

/-- The already derived full Fourier-budget bridge discharges the finite
Serrin premise on the same physical front.
-/
theorem local_front_leray_hopf_identification_of_fourier_budget
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hbudget : FourierBudgetFinite (fun r => datumFourierCoeff (u r)) T) :
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  local_front_leray_hopf_identification_of_serrin ν T a u p v G H hv
    (local_front_fourier_budget_to_serrin ν T a u p H hbudget)

/-- Q01 supplies an original weak trajectory and the physical finite-front
comparison identifies it with the given front. This does not construct the
front, extend it, or assert global smoothness.
-/
theorem local_front_original_leray_hopf_of_fourier_budget
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun r => datumFourierCoeff (u r)) T) :
    ∃ (v : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) v G ∧
      v 0 =ᵐ[volume.restrict unitCube] a ∧
      ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r := by
  obtain ⟨v, G, hv, hinitial⟩ :=
    smooth_datum_lerayHopf_exists ν H.viscosity_pos a H.initial_smooth
  exact ⟨v, G, hv, hinitial,
    local_front_leray_hopf_identification_of_fourier_budget
      ν T a u p v G H hv hbudget⟩

end

end MethbokeAddon.WeakFouriermanB
