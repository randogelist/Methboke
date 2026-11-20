import MethbokeAddon.FeffermanFamily.DisjointGerms
import MethbokeAddon.FeffermanFamily.LocalDifferential

/-!
# Exact native NSE assembly on finitely many disjoint carriers

Every velocity, pressure and force has the same fixed spatial carrier for all
times. At an active carrier the sum agrees locally with that copy; outside
all carriers it agrees locally with zero. Locality therefore transfers the
actual nonlinear equation without adding an interaction force.

The time set is arbitrary and may include zero. `timeDerivative` remains the
native `derivWithin` on `Ici 0`. These are conditional assembly lemmas, not
existence, smoothness, support-packing, energy or uniqueness theorems.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped BigOperators Topology

namespace MethbokeAddon.FeffermanFamily

noncomputable section

/-- Finite disjoint assembly preserves the actual native divergence equation. -/
theorem finite_sum_native_divergence_free
    {ι : Type*} [Fintype ι] {K : ι → Set Vec} {u : ι → Velocity}
    {times : Set ℝ}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i t x, x ∉ K i → u i t x = 0)
    (hdiv : ∀ i, ∀ t ∈ times, ∀ x : Vec, divergence (u i t) x = 0) :
    ∀ t ∈ times, ∀ x : Vec,
      divergence (fun y => ∑ i, u i t y) x = 0 := by
  intro t ht x
  classical
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hxi⟩ := hx
    have hu := finite_sum_spacetime_eventuallyEq_active
      hclosed hdisjoint hzero hxi t
    exact (nativeDivergence_congr hu).trans (hdiv i t ht x)
  · have hout : ∀ i, x ∉ K i := fun i hi => hx ⟨i, hi⟩
    have hu := finite_sum_spacetime_eventuallyEq_zero hclosed hzero hout t
    rw [nativeDivergence_congr (v := (0 : Velocity)) hu]
    simp [divergence, coordinateDerivative]

/-- Finite disjoint assembly solves the same-viscosity forced equation with
exactly the sum of the prescribed forces, including at initial time if requested. -/
theorem finite_sum_native_forcedNSE
    {ι : Type*} [Fintype ι] {K : ι → Set Vec}
    {u F : ι → Velocity} {p : ι → Pressure} {times : Set ℝ} (ν : ℝ)
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (huzero : ∀ i t x, x ∉ K i → u i t x = 0)
    (hpzero : ∀ i t x, x ∉ K i → p i t x = 0)
    (hFzero : ∀ i t x, x ∉ K i → F i t x = 0)
    (hNS : ∀ i, ∀ t ∈ times, ∀ x : Vec,
      timeDerivative (u i) t x + convection (u i t) x +
          SingularClosure.gradient (p i t) x =
        ν • laplacian (u i t) x + F i t x) :
    ∀ t ∈ times, ∀ x : Vec,
      timeDerivative (fun s y => ∑ i, u i s y) t x +
          convection (fun y => ∑ i, u i t y) x +
          SingularClosure.gradient (fun y => ∑ i, p i t y) x =
        ν • laplacian (fun y => ∑ i, u i t y) x + ∑ i, F i t x := by
  intro t ht x
  classical
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hxi⟩ := hx
    have hu := finite_sum_spacetime_eventuallyEq_active
      hclosed hdisjoint huzero hxi t
    have hp := finite_sum_spacetime_eventuallyEq_active
      hclosed hdisjoint hpzero hxi t
    have hF := finite_sum_spacetime_eventuallyEq_active
      hclosed hdisjoint hFzero hxi t
    exact (nativeForcedEquation_congr ν hu hp hF).mpr (hNS i t ht x)
  · have hout : ∀ i, x ∉ K i := fun i hi => hx ⟨i, hi⟩
    have hu := finite_sum_spacetime_eventuallyEq_zero hclosed huzero hout t
    have hp := finite_sum_spacetime_eventuallyEq_zero hclosed hpzero hout t
    have hF := finite_sum_spacetime_eventuallyEq_zero hclosed hFzero hout t
    exact (nativeForcedEquation_congr ν (v := (0 : Velocity))
      (q := (0 : Pressure)) (G := (0 : Velocity)) hu hp hF).mpr
      (nativeForcedEquation_zero ν t x)

end

end MethbokeAddon.FeffermanFamily
