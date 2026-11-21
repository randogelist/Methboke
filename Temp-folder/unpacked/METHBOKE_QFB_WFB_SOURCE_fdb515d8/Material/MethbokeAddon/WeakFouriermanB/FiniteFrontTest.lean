import MethbokeAddon.WeakFouriermanB.LocalFront
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
An actual finite physical front supplies globally admissible smooth weak
momentum tests that agree with the front through any shorter positive time.

A smooth time map freezes late times inside the given front and preserves
all sufficiently early times. This extends the admissible test, not the NSE
solution. No extension/continuation field is assumed. In particular, the
same test preserves the strong initial trace of the original velocity.

Prepared source only; matching external cached verification is pending.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- Equal to the identity near zero and equal to `c` outside the bump. -/
def finiteFrontTimeClamp (c : ℝ) (b : ContDiffBump (0 : ℝ)) (r : ℝ) : ℝ :=
  c + b r * (r - c)

theorem finiteFrontTimeClamp_contDiff (c : ℝ) (b : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (finiteFrontTimeClamp c b) := by
  exact contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const))

/-- Positive times remain strictly inside the front. No assertion about
negative-time smoothness of the original velocity is needed. -/
theorem finiteFrontTimeClamp_mem_Ioo {c T : ℝ} (b : ContDiffBump (0 : ℝ))
    (hc : c ∈ Ioo (0 : ℝ) T) (houter : b.rOut < T)
    (r : ℝ) (hr : 0 < r) :
    finiteFrontTimeClamp c b r ∈ Ioo (0 : ℝ) T := by
  by_cases hb : b r = 0
  · simpa only [finiteFrontTimeClamp, hb, zero_mul, add_zero] using hc
  · have hrball : r ∈ Metric.ball (0 : ℝ) b.rOut := by
      rw [← b.support_eq]
      exact hb
    have habs : |r| < b.rOut := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hrball
    have hrT : r < T := (le_abs_self r).trans_lt (habs.trans houter)
    have hb0 : 0 ≤ b r := b.nonneg
    have hb1 : b r ≤ 1 := b.le_one
    have hbpos : 0 < b r := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hbrem : 0 ≤ 1 - b r := sub_nonneg.mpr hb1
    change 0 < c + b r * (r - c) ∧ c + b r * (r - c) < T
    constructor
    · nlinarith only [mul_pos hbpos hr, mul_nonneg hbrem hc.1.le]
    · nlinarith only [mul_pos hbpos (sub_pos.mpr hrT),
        mul_nonneg hbrem (sub_nonneg.mpr hc.2.le)]

/-- A finite physical front supplies one genuine global positive smooth
solenoidal test agreeing locally at every time up to the shorter horizon,
including near zero. The test is not asserted to solve NSE at later times. -/
theorem local_front_exists_global_test_through
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T) :
    ∃ φ : Velocity, CriticalPositiveSolenoidalTest φ ∧
      (∀ r ∈ Ioc (0 : ℝ) t, φ =ᶠ[𝓝 r] u) ∧ φ =ᶠ[𝓝 (0 : ℝ)] u := by
  let c : ℝ := T / 2
  have hc : c ∈ Ioo (0 : ℝ) T := by
    dsimp [c]
    constructor <;> linarith
  let b : ContDiffBump (0 : ℝ) :=
    ⟨(t + T) / 2, (t + 3 * T) / 4, by linarith, by linarith⟩
  have houter : b.rOut < T := by
    dsimp [b]
    linarith
  have hinner : ∀ r ∈ Ioc (0 : ℝ) t, r ∈ Metric.ball (0 : ℝ) b.rIn := by
    intro r hr
    apply Metric.mem_ball.mpr
    rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]
    change r < (t + T) / 2
    linarith [hr.2]
  let ρ : ℝ → ℝ := finiteFrontTimeClamp c b
  have hρ : ContDiff ℝ ∞ ρ := finiteFrontTimeClamp_contDiff c b
  have hrange : ∀ r : ℝ, 0 < r → ρ r ∈ Ioo (0 : ℝ) T :=
    finiteFrontTimeClamp_mem_Ioo b hc houter
  let φ : Velocity := fun r x => u (ρ r) x
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × Vec => (ρ z.1, z.2)) :=
    (hρ.comp contDiff_fst).prodMk contDiff_snd
  have hφ : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => φ z.1 z.2) {z | 0 < z.1} := by
    intro z hz
    have hfront := H.velocity_smooth.contDiffAt
      ((localFrontSpacetime_isOpen T).mem_nhds
        (show (ρ z.1, z.2) ∈ localFrontSpacetime T from hrange z.1 hz))
    have hcomp : ContDiffAt ℝ ∞ (fun q : ℝ × Vec => φ q.1 q.2) z := by
      simpa only [φ, Function.comp_def] using hfront.comp z hmap.contDiffAt
    exact hcomp.contDiffWithinAt
  have hagree (r : ℝ) (hr : r ∈ Metric.ball (0 : ℝ) b.rIn) :
      φ =ᶠ[𝓝 r] u := by
    have heq := b.eventuallyEq_one_of_mem_ball hr
    filter_upwards [heq] with q hq
    change b q = 1 at hq
    change u (ρ q) = u q
    have hρq : ρ q = q := by
      change c + b q * (q - c) = q
      rw [hq]
      ring
    rw [hρq]
  refine ⟨φ, ⟨hφ, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    exact H.velocity_periodic (ρ r) (hrange r hr)
  · intro r hr x
    exact H.divergence_free (ρ r) (hrange r hr) x
  · intro r hr
    exact hagree r (hinner r hr)
  · exact hagree 0 (Metric.mem_ball_self b.rIn_pos)

/-- In particular, every compact inner window admits an actual global
positive smooth solenoidal test agreeing in a time neighborhood of the window. -/
theorem local_front_exists_global_test_on_compact
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    ∃ φ : Velocity, CriticalPositiveSolenoidalTest φ ∧
      ∀ r ∈ Icc s t, φ =ᶠ[𝓝 r] u := by
  obtain ⟨φ, hφ, hagree, _⟩ := local_front_exists_global_test_through
    ν T a u p H t (hs.trans_le hst) ht
  exact ⟨φ, hφ, fun r hr => hagree r ⟨hs.trans_le hr.1, hr.2⟩⟩

/-- Time-neighborhood equality of physical fields preserves the literal
within-nonnegative-time derivative used in the NSE equation. -/
theorem local_test_timeDerivative_eq_of_eventuallyEq
    {φ u : Velocity} {r : ℝ} (h : φ =ᶠ[𝓝 r] u) (x : Vec) :
    timeDerivative φ r x = timeDerivative u r x := by
  have hx : (fun q => φ q x) =ᶠ[𝓝 r] (fun q => u q x) := by
    filter_upwards [h] with q hq
    exact congrFun hq x
  exact hx.derivWithin_eq_of_nhds

end

end MethbokeAddon.WeakFouriermanB
