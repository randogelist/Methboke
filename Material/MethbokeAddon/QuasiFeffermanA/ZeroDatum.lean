import MethbokeAddon.QuasiFeffermanA.PhysicalRoot
import MethbokeAddon.QuasiFeffermanA.PhysicalH1
import MethbokeAddon.QuasiFeffermanA.Energy
import MethbokeAddon.QuasiFeffermanA.LHRestart

/-!
# The full physical QFA conclusion for the zero datum

The actual zero weak solution is constructed field by field. For every other
supplied zero-datum Leray--Hopf path, the existing energy bound forces its L2
velocity to vanish at every nonnegative time. Positive viscosity also forces
the original weak-gradient dissipation to integrate to zero on every finite
tail interval. This supplies every energy start, full translated PDE class
membership, and uniqueness against every future from the exact trace.

The smooth representative and point-normalized pressure are the genuine zero
fields, satisfying the actual Euclidean NSE operators. Equality to the Lp
representative is only asserted spatially almost everywhere at each time.
No pointwise identity for an arbitrarily selected Lp representative is used.

This closes the exact physical zero-datum conclusion, including the closed
cutoff delta=0 and nonemptiness. It is not the all-data QFA theorem.
Prepared source requires matching authorized external compiler and named
type/axiom evidence. No local Lean, Lake, or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Interval Topology

namespace MethbokeAddon.QuasiFeffermanA.ZeroDatum

open QFA.Representation
open PhysicalRoot

def zeroVelocity : Velocity := fun _ => 0

def zeroGradient : WeakGradient := fun _ _ => 0

theorem zero_solenoidal : Solenoidal (0 : SpatialL2) := by
  apply (solenoidal_iff_testCLM (0 : SpatialL2)).mpr
  intro φ
  exact (solenoidalTestCLM φ).map_zero

theorem zero_spatialWeakGradient :
    SpatialWeakGradient (0 : SpatialL2) (fun _ : Fin 3 => 0) := by
  simpa only [map_zero] using physicalH1_weakGradient (0 : PhysicalH1)

private theorem zero_timeIntegrand_ae (φ : MomentumTest) (t : ℝ) :
    momentumTimeIntegrand zeroVelocity φ t =ᵐ[volume] (0 : Space → ℝ) := by
  filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx
  simp only [momentumTimeIntegrand, zeroVelocity, hx, Pi.zero_apply, inner_zero_left]

private theorem zero_convectionIntegrand_ae (φ : MomentumTest) (t : ℝ) :
    momentumConvectionIntegrand zeroVelocity φ t =ᵐ[volume] (0 : Space → ℝ) := by
  filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx
  simp only [momentumConvectionIntegrand, zeroVelocity, hx, Pi.zero_apply,
    inner_zero_left, mul_zero, Finset.sum_const_zero]

private theorem zero_dissipationIntegrand_ae (φ : MomentumTest) (t : ℝ) :
    momentumDissipationIntegrand zeroGradient φ t =ᵐ[volume] (0 : Space → ℝ) := by
  filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx
  simp only [momentumDissipationIntegrand, zeroGradient, hx, Pi.zero_apply,
    inner_zero_left, Finset.sum_const_zero]

private theorem zero_timeIntegral (φ : MomentumTest) (t : ℝ) :
    (∫ x : Space, momentumTimeIntegrand zeroVelocity φ t x) = 0 := by
  rw [integral_congr_ae (zero_timeIntegrand_ae φ t)]
  exact integral_zero _ _

private theorem zero_convectionIntegral (φ : MomentumTest) (t : ℝ) :
    (∫ x : Space, momentumConvectionIntegrand zeroVelocity φ t x) = 0 := by
  rw [integral_congr_ae (zero_convectionIntegrand_ae φ t)]
  exact integral_zero _ _

private theorem zero_dissipationIntegral (φ : MomentumTest) (t : ℝ) :
    (∫ x : Space, momentumDissipationIntegrand zeroGradient φ t x) = 0 := by
  rw [integral_congr_ae (zero_dissipationIntegrand_ae φ t)]
  exact integral_zero _ _

/-- The actual zero pair satisfies the entire weak momentum contract,
including genuine spatial and time integrability. -/
theorem zero_weakMomentum (ν : ℝ) : WeakMomentum ν zeroVelocity zeroGradient := by
  constructor
  · intro φ t _
    exact ⟨integrable_zero.congr (zero_timeIntegrand_ae φ t).symm,
      integrable_zero.congr (zero_convectionIntegrand_ae φ t).symm,
      integrable_zero.congr (zero_dissipationIntegrand_ae φ t).symm⟩
  · intro φ
    simp only [zero_timeIntegral, zero_convectionIntegral, zero_dissipationIntegral]
    exact ⟨integrable_zero, integrable_zero, integrable_zero⟩
  · intro φ
    simp only [zero_timeIntegral, zero_convectionIntegral, zero_dissipationIntegral,
      integral_zero, zero_add, mul_zero, sub_self]

/-- A concrete full Leray--Hopf witness from zero, with no existence premise. -/
theorem zero_lerayHopf (ν : ℝ) : LerayHopf ν 0 zeroVelocity zeroGradient := by
  refine {
    momentum := zero_weakMomentum ν
    initial := rfl
    solenoidal := fun _ _ => zero_solenoidal
    velocity_aestronglyMeasurable := fun _ _ => aestronglyMeasurable_const
    gradient_memLp := fun _ _ _ => MemLp.zero'
    spatial_weak_gradient := ?_
    weak_continuity := ?_
    energy_initial := ?_
    energy_starts := ?_
  }
  · intro R _
    exact Eventually.of_forall (fun _ => zero_spatialWeakGradient)
  · intro b
    exact continuousOn_const
  · intro t _
    simp [zeroVelocity, zeroGradient, velocityEnergy, gradientEnergy]
  · intro R _
    filter_upwards with s
    intro r _
    simp [zeroVelocity, zeroGradient, velocityEnergy, gradientEnergy]

/-- Zero velocity and the zero pressure satisfy the native classical PDE
and point gauge on every closed tail. -/
theorem zero_classicalTail (ν δ : ℝ) :
    ClassicalTail ν δ (0 : SingularClosure.Velocity) (0 : SingularClosure.Pressure) := by
  refine ⟨contDiffOn_const, contDiffOn_const, ?_, ?_, ?_⟩
  · intro t _ x
    simp [SingularClosure.divergence, SingularClosure.coordinateDerivative]
  · intro t _ x
    have hDerivative (i : Fin 3) :
        SingularClosure.coordinateDerivative (0 : SingularClosure.Field) i = 0 := by
      funext y
      simp [SingularClosure.coordinateDerivative]
    have hGradient : SingularClosure.gradient (0 : Space → ℝ) x = 0 := by
      ext i
      change (fderiv ℝ (0 : Space → ℝ) x) (SingularClosure.unitVector i) = 0
      simp
    change SingularClosure.timeDerivative (0 : SingularClosure.Velocity) t x +
      SingularClosure.convection (0 : SingularClosure.Field) x +
        SingularClosure.gradient (0 : Space → ℝ) x =
          ν • SingularClosure.laplacian (0 : SingularClosure.Field) x
    simp [SingularClosure.timeDerivative, SingularClosure.convection, hGradient,
      SingularClosure.laplacian, hDerivative]
  · intro t _
    rfl

@[simp] theorem cutoff_zero (ν : ℝ) : PhysicalRoot.cutoff ν (0 : SpatialL2) = 0 := by
  simp [PhysicalRoot.cutoff]

/-- Every specified zero-datum L2 velocity vanishes at every nonnegative time. -/
theorem zeroDatum_velocity_eq_zero {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) : u t = 0 :=
  h.eq_zero_of_initial_eq_zero hν rfl ht

/-- Positive viscosity forces the original supplied weak-gradient integral
to vanish; no pointwise assertion about its arbitrary time representative is used. -/
theorem zeroDatum_initial_dissipation_eq_zero
    {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) = 0 := by
  have hD : 0 ≤ ∫ r in (0 : ℝ)..t, gradientEnergy (G r) :=
    intervalIntegral.integral_nonneg_of_forall ht (fun r => gradientEnergy_nonneg (G r))
  have he := h.energy_initial t ht
  rw [zeroDatum_velocity_eq_zero h hν.le ht] at he
  simp only [velocityEnergy, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at he
  have hDle : (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) ≤ 0 := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * ν by positivity)).mp
    simpa only [mul_zero] using he
  exact le_antisymm hDle hD

/-- Every finite tail has zero dissipation in the same original weak-gradient
witness, using genuine interval integrability before interval subtraction. -/
theorem zeroDatum_tail_dissipation_eq_zero
    {ν δ t : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) (hδ : 0 ≤ δ) (ht : δ ≤ t) :
    (∫ r in δ..t, gradientEnergy (G r)) = 0 := by
  have ht0 : 0 ≤ t := hδ.trans ht
  have ht1 : 0 < t + 1 := by linarith
  have hI := h.energyProfile.gradientEnergy_intervalIntegrable ht1
  have h0δ : IntervalIntegrable (fun r => gradientEnergy (G r)) volume (0 : ℝ) δ := by
    apply hI.mono_set
    rw [uIcc_of_le hδ, uIcc_of_le ht1.le]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hδt : IntervalIntegrable (fun r => gradientEnergy (G r)) volume δ t := by
    apply hI.mono_set
    rw [uIcc_of_le ht, uIcc_of_le ht1.le]
    exact Icc_subset_Icc hδ (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0δ hδt
  rw [zeroDatum_initial_dissipation_eq_zero h hν hδ,
    zeroDatum_initial_dissipation_eq_zero h hν ht0, zero_add] at hadd
  exact hadd

theorem zeroDatum_tailEnergyEquality
    {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    TailEnergyEquality ν u G δ := by
  intro t ht
  change ‖u t‖ ^ 2 + 2 * ν * (∫ r in δ..t, gradientEnergy (G r)) = ‖u δ‖ ^ 2
  rw [zeroDatum_velocity_eq_zero h hν.le (hδ.trans ht),
    zeroDatum_velocity_eq_zero h hν.le hδ,
    zeroDatum_tail_dissipation_eq_zero h hν hδ ht]
  simp

/-- Every nonnegative time, including zero, is an energy start for this path. -/
theorem zeroDatum_energyStart
    {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    EnergyStart ν u G δ := by
  intro t ht
  exact (zeroDatum_tailEnergyEquality h hν hδ t ht).le

theorem zeroDatum_hasSmoothTail
    {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 ≤ ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    HasSmoothTail ν u δ := by
  refine ⟨0, 0, zero_classicalTail ν δ, ?_⟩
  intro t ht
  rw [zeroDatum_velocity_eq_zero h hν (hδ.trans ht)]
  exact Lp.coeFn_zero Space 2 (volume : Measure Space)

/-- Full translated weak PDE membership and same-L2-velocity uniqueness are
derived for every future from the exact own zero trace. -/
theorem zeroDatum_uniqueFuture
    {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    UniqueFuture ν u G δ := by
  constructor
  · have hshift := h.timeTranslate hδ (zeroDatum_energyStart h hν hδ)
    simpa only [QFA.Endpoints.Restart.timeTranslate, add_comm] using hshift
  · intro v H hv t ht
    change u (δ + t) = v t
    have htrace : u δ = 0 := zeroDatum_velocity_eq_zero h hν.le hδ
    exact (zeroDatum_velocity_eq_zero h hν.le (add_nonneg hδ ht)).trans
      (hv.eq_zero_of_initial_eq_zero hν.le htrace ht).symm

/-- Complete physical QFA for zero datum, including delta=cutoff=0,
actual weak-solution existence, original-gradient tail energy and all futures. -/
theorem closedDatumConclusion_zero (ν : ℝ) (hν : 0 < ν) :
    ClosedDatumConclusion ν (0 : SpatialL2) := by
  refine ⟨⟨zeroVelocity, zeroGradient, zero_lerayHopf ν⟩, ?_⟩
  intro u G h δ hδ
  have hδ0 : 0 ≤ δ := by simpa only [cutoff_zero] using hδ
  exact ⟨zeroDatum_hasSmoothTail h hν.le hδ0,
    zeroDatum_tailEnergyEquality h hν hδ0, zeroDatum_uniqueFuture h hν hδ0⟩

/-- The registered strict-cutoff physical conclusion follows for zero datum. -/
theorem datumConclusion_zero (ν : ℝ) (hν : 0 < ν) :
    DatumConclusion ν (0 : SpatialL2) :=
  (closedDatumConclusion_zero ν hν).strict

end MethbokeAddon.QuasiFeffermanA.ZeroDatum
