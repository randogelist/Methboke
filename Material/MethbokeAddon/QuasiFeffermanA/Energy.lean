import MethbokeAddon.QuasiFeffermanA.Contracts
import QFA.Assembly.Restart

/-!
# Native whole-space QFA: energy and strong-trace adapters

These theorems apply the recovered scalar weighted-energy and Hilbert-trace
proofs to the concrete whole-space Leray--Hopf contract. The finite-horizon
product is genuinely integrable. At an admissible energy start the translated
path has the recovered energy/trace data; this does not assert translated
weak momentum or full Leray--Hopf membership.

No existence, Sobolev constant, continuation, comparison, or eventual
regularity theorem is claimed here. Matching external compilation and exact
type/axiom audits are required before accepting this prepared source.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Topology

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Representation

/-- The native energy-start predicate is exactly the recovered scalar one. -/
theorem energyStart_iff_qfa
    {ν s : ℝ} {u : Velocity} {G : WeakGradient} :
    EnergyStart ν u G s ↔ QFA.Assembly.Restart.EnergyStart ν u G s := Iff.rfl

/-- Only the three actual energy-class fields are needed for this adapter. -/
theorem LerayHopf.energyProfile
    {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) : EnergyProfile ν a u G := by
  exact ⟨h.velocity_aestronglyMeasurable, h.gradient_memLp, h.energy_initial⟩

/-- The exact initial trace is solenoidal in the concrete full-volume sense. -/
theorem LerayHopf.initial_solenoidal
    {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) : Solenoidal a := by
  simpa only [h.initial] using h.solenoidal 0 (le_refl 0)

/-- Nonnegative dissipation gives the pointwise initial-energy upper bound. -/
theorem LerayHopf.velocity_energy_le_initial
    {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) :
    velocityEnergy (u t) ≤ velocityEnergy a := by
  have hD : 0 ≤ ∫ r in (0 : ℝ)..t, gradientEnergy (G r) :=
    intervalIntegral.integral_nonneg_of_forall ht
      (fun r => gradientEnergy_nonneg (G r))
  have hprod : 0 ≤ 2 * ν * (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) :=
    mul_nonneg (mul_nonneg (by norm_num) hν) hD
  linarith only [h.energy_initial t ht, hprod]

/-- The actual whole-space energy--enstrophy product is integrable on every
finite positive interval and has the exact factor-one-quarter budget. -/
theorem LerayHopf.energy_product_budget_Ioo
    {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 < ν) (hR : 0 < R) :
    Integrable (fun t => velocityEnergy (u t) * gradientEnergy (G t))
        (volume.restrict (Ioo (0 : ℝ) R)) ∧
      (∫ t in Ioo (0 : ℝ) R, velocityEnergy (u t) * gradientEnergy (G t)) ≤
        ‖a‖ ^ 4 / (4 * ν) := by
  exact h.energyProfile.energy_product_budget_Ioo hν hR

/-- Zero is an admissible energy start because the initial L2 trace is exact. -/
theorem LerayHopf.energyStart_zero
    {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) : EnergyStart ν u G 0 := by
  intro r hr
  simpa only [h.initial] using h.energy_initial r hr

/-- Strong right continuity at a supplied energy start is derived from weak
continuity and the energy inequality; it is not assumed in the class. -/
theorem LerayHopf.strong_right_trace
    {ν s : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hstart : EnergyStart ν u G s) :
    Tendsto u (𝓝[>] s) (𝓝 (u s)) := by
  exact QFA.Endpoints.Restart.strong_right_trace_of_energy_start
    hν hs (fun r _ => gradientEnergy_nonneg (G r))
    (h.weak_continuity (u s)) hstart

/-- The prescribed initial datum is attained strongly from positive time. -/
theorem LerayHopf.strong_initial_trace
    {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  simpa only [h.initial] using
    h.strong_right_trace hν (le_refl 0) h.energyStart_zero

/-- A supplied nonnegative energy start gives the exact translated energy
profile, weak pairing continuity, and right strong trace. This is energy data,
not a proof of membership in the shifted physical PDE class. -/
theorem LerayHopf.restart_energy_data
    {ν s : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hstart : EnergyStart ν u G s) :
    QFA.Assembly.Restart.RestartData ν u G s := by
  exact QFA.Assembly.Restart.restartData_of_energyStart
    h.energyProfile hν hs h.weak_continuity
    (energyStart_iff_qfa.mp hstart)

/-- The standard a.e. class fields intersect to provide actual solenoidal
weak-gradient traces and the proved energy/strong-trace restart data. -/
theorem LerayHopf.ae_restart_energy_data
    {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
        EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s := by
  have htime : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R), s ∈ Ioo (0 : ℝ) R :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [htime, h.spatial_weak_gradient R hR, h.energy_starts R hR]
    with s hs hgradient hstart
  exact ⟨h.solenoidal s hs.1.le, hgradient, hstart,
    h.restart_energy_data hν hs.1.le hstart⟩

/-- Zero datum forces the specified L2 velocity to vanish at every
nonnegative time. This does not construct a solution or a pressure. -/
theorem LerayHopf.eq_zero_of_initial_eq_zero
    {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (ha : a = 0)
    {t : ℝ} (ht : 0 ≤ t) : u t = 0 := by
  have hsq : ‖u t‖ ^ 2 ≤ 0 := by
    simpa [ha, velocityEnergy] using h.velocity_energy_le_initial hν ht
  have hnorm : ‖u t‖ = 0 := by nlinarith [norm_nonneg (u t)]
  exact norm_eq_zero.mp hnorm

end MethbokeAddon.QuasiFeffermanA
