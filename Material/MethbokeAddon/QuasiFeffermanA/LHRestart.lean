import MethbokeAddon.QuasiFeffermanA.Integration
import MethbokeAddon.QuasiFeffermanA.MomentumTranslation

/-!
# Full whole-space Leray--Hopf restart for supplied paths

The exact original weak momentum equation is transported by the constructed
test-translation theorem. The remaining original Leray--Hopf fields are
transported from the supplied path, including a.e. weak derivatives and the
energy inequality at every upper endpoint for almost every start.

This closes shifted class membership and upgrades the existing safe-window
selection. It does not construct an original weak solution, a strong local
solution, a Sobolev constant, a smooth tail, or weak--strong comparison.

Prepared for matching authorized external compiler/type/axiom evidence.
No local Lean, Lake or kernel execution is authorized.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Topology

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Representation QFA.Endpoints.Restart

/-- Pull back an arbitrary a.e. predicate on the original finite time interval. -/
theorem timeTranslate_ae_Ioo {P : ℝ → Prop} {s R : ℝ} (hs : 0 ≤ s)
    (hP : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (R + s)), P t) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), P (t + s) := by
  rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at hP ⊢
  exact QFA.Endpoints.Restart.timeTranslate_ae_Ioc hs hP

/-- All upper endpoints remain quantified after transporting an energy start. -/
theorem energyStart_timeTranslate {ν s r : ℝ} {u : Velocity} {G : WeakGradient}
    (hstart : EnergyStart ν u G (r + s)) :
    EnergyStart ν (timeTranslate s u) (timeTranslate s G) r := by
  intro t ht
  change velocityEnergy (u (t + s)) +
    2 * ν * (∫ q in r..t, gradientEnergy (G (q + s))) ≤
      velocityEnergy (u (r + s))
  rw [intervalIntegral.integral_comp_add_right (fun q => gradientEnergy (G q)) s]
  exact hstart (t + s) (add_le_add_right ht s)

/-- Full native shifted-LH membership at every supplied nonnegative energy start.
No positivity of viscosity is required merely to translate the class. -/
theorem LerayHopf.timeTranslate {ν s : ℝ} {a : SpatialL2}
    {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hs : 0 ≤ s) (hstart : EnergyStart ν u G s) :
    LerayHopf ν (u s) (timeTranslate s u) (timeTranslate s G) := by
  have hprofile := QFA.Assembly.Restart.energyProfile_timeTranslate
    h.energyProfile hs (energyStart_iff_qfa.mp hstart)
  refine {
    momentum := h.momentum.timeTranslate hs
    initial := by simp only [timeTranslate, zero_add]
    solenoidal := fun t ht => h.solenoidal (t + s) (add_nonneg ht hs)
    velocity_aestronglyMeasurable := hprofile.velocity_aestronglyMeasurable
    gradient_memLp := hprofile.gradient_memLp
    spatial_weak_gradient := ?_
    weak_continuity := QFA.Assembly.Restart.timeTranslate_weakPairingContinuousOn
      hs h.weak_continuity
    energy_initial := hprofile.zero_start_energy
    energy_starts := ?_
  }
  · intro R hR
    have hRs : 0 < R + s := add_pos_of_pos_of_nonneg hR hs
    exact timeTranslate_ae_Ioo hs (h.spatial_weak_gradient (R + s) hRs)
  · intro R hR
    have hRs : 0 < R + s := add_pos_of_pos_of_nonneg hR hs
    have hshift := timeTranslate_ae_Ioo hs (h.energy_starts (R + s) hRs)
    filter_upwards [hshift] with r hr
    exact energyStart_timeTranslate hr

/-- Almost every time in any finite positive window gives full shifted physical
membership as well as a solenoidal weak-gradient trace and an energy start. -/
theorem LerayHopf.ae_full_restart {ν R : ℝ} {a : SpatialL2}
    {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
        EnergyStart ν u G s ∧
        LerayHopf ν (u s) (timeTranslate s u) (timeTranslate s G) := by
  have htime : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R), s ∈ Ioo (0 : ℝ) R :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [htime, h.spatial_weak_gradient R hR, h.energy_starts R hR]
    with s hs hgradient hstart
  exact ⟨h.solenoidal s hs.1.le, hgradient, hstart,
    h.timeTranslate hs.1.le hstart⟩

/-- The accepted energy/trace restart predicate and full shifted PDE membership
hold simultaneously at almost every start. -/
theorem LerayHopf.goodRestart_and_full_restart_ae {ν R : ℝ} {a : SpatialL2}
    {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      GoodRestart ν u G s ∧
        LerayHopf ν (u s) (timeTranslate s u) (timeTranslate s G) := by
  filter_upwards [h.goodRestart_ae hν hR, h.ae_full_restart hR]
    with s hgood hfull
  exact ⟨hgood, hfull.2.2.2⟩

/-- At least half of the original safe window consists of actual full PDE
restarts with the original strict product threshold. The scalar S still
requires independent Sobolev admissibility before a continuation application. -/
theorem LerayHopf.safe_window_full_restart_and_measure
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    (safeCutoff S ‖a‖ ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S ‖a‖ ν))).real
        {s | (GoodRestart ν u G s ∧
          LerayHopf ν (u s) (timeTranslate s u) (timeTranslate s G)) ∧
          velocityEnergy (u s) * gradientEnergy (G s) < productThreshold S ν}) ∧
      ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧
        (GoodRestart ν u G s ∧
          LerayHopf ν (u s) (timeTranslate s u) (timeTranslate s G)) ∧
        velocityEnergy (u s) * gradientEnergy (G s) < productThreshold S ν := by
  have hM : ‖a‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr ha)
  have hR : 0 < safeCutoff S ‖a‖ ν := safeCutoff_pos hS hν hM
  obtain ⟨hprod, hbudget⟩ := h.energy_product_budget_Ioo hν hR
  have hgood := h.goodRestart_and_full_restart_ae hν.le hR
  have hprodnn : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S ‖a‖ ν)),
      0 ≤ velocityEnergy (u s) * gradientEnergy (G s) := by
    filter_upwards with s
    exact mul_nonneg (velocityEnergy_nonneg (u s)) (gradientEnergy_nonneg (G s))
  exact ⟨good_set_measure_ge_half_of_product_budget hS hν hprod hprodnn hgood hbudget,
    exists_good_time_of_product_budget hS hν hM hprod hgood hbudget⟩

/-- The selected interior trace now restarts the actual full Leray--Hopf PDE
class, while retaining the previously established strong trace and strict bound. -/
theorem LerayHopf.exists_safe_full_restart
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
      EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s ∧
      LerayHopf ν (u s) (timeTranslate s u) (timeTranslate s G) ∧
      Tendsto u (𝓝[>] s) (𝓝 (u s)) ∧
      velocityEnergy (u s) * gradientEnergy (G s) < productThreshold S ν := by
  obtain ⟨s, hs0, hsR, hsol, hgrad, hstart, hdata, htrace, hsmall⟩ :=
    h.exists_safe_restart hS hν ha
  exact ⟨s, hs0, hsR, hsol, hgrad, hstart, hdata,
    h.timeTranslate hs0.le hstart, htrace, hsmall⟩

end MethbokeAddon.QuasiFeffermanA
