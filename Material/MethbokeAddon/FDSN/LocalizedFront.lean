import MethbokeAddon.FDSN.LocalizedResidual

/-!
# The concrete localized family solves the actual preterminal NSE

At positive times this is the residual identity. At time zero the closed
support is separated from the initial time, so native derivative locality
transports the seed equation, including its `derivWithin (Ici 0)` convention.
-/

set_option autoImplicit false

noncomputable section

open Set Filter SingularClosure
open MethbokeAddon.FeffermanFamily
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

theorem localizedPair_momentum
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      timeDerivative (localizedPairVelocity a β u lambda) t x +
          convection (localizedPairVelocity a β u lambda t) x +
          SingularClosure.gradient (p t) x =
        ν • laplacian (localizedPairVelocity a β u lambda t) x +
          localizedPairForce ν a β u F lambda t x := by
  intro t ht x
  by_cases htzero : t = 0
  · subst t
    have hβzero : (0 : ℝ) ∉ tsupport β := by
      intro hmem
      exact (lt_irrefl (0 : ℝ)) (hβs hmem).1
    have hc : (fun z : ℝ × Vec => localizedPairCorrection a β u lambda z.1 z.2)
        =ᶠ[𝓝 (0, x)] 0 :=
      velocity_zero_germ_of_notMem_timeSupport (localizedPairCorrection a β u lambda)
        (fun hmem => hβzero (localizedPairCorrection_tsupport_subset a β u lambda hmem)) x
    have hv : (fun z : ℝ × Vec => localizedPairVelocity a β u lambda z.1 z.2)
        =ᶠ[𝓝 (0, x)] (fun z => u z.1 z.2) := by
      apply hc.mono
      intro z hz
      change localizedPairCorrection a β u lambda z.1 z.2 = 0 at hz
      change u z.1 z.2 + localizedPairCorrection a β u lambda z.1 z.2 = u z.1 z.2
      rw [hz, add_zero]
    have hforce : localizedPairForce ν a β u F lambda 0 x = F 0 x :=
      residualForce_eq_of_zero_germ ν u F (localizedPairCorrection a β u lambda) 0 x hc
    rw [nativeTimeDerivative_congr hv, nativeConvection_congr hv,
      nativeLaplacian_congr hv, hforce]
    exact h.front.equation 0 ht x
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
    have hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
        {z | z.1 ∈ Ioo (0 : ℝ) T} :=
      h.front.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
    exact native_residual_momentum_on_open_slab ν u F (localizedPairCorrection a β u lambda)
      p 0 T hU (localizedPairCorrection_smooth h a hβ hβs lambda).contDiffOn
      (fun s hs y => h.front.equation s ⟨hs.1.le, hs.2⟩ y) t ⟨htpos, ht.2⟩ x

/-- The complete preterminal record for the constructed velocity and forcing,
with the seed pressure and viscosity unchanged. -/
theorem localizedPair_front
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    PreterminalNSE ν T (localizedPairVelocity a β u lambda) p
      (localizedPairForce ν a β u F lambda) := by
  refine {
    velocity_smooth := h.front.velocity_smooth.add
      (localizedPairCorrection_smooth h a hβ hβs lambda).contDiffOn
    pressure_smooth := h.front.pressure_smooth
    velocity_periodic := ?_
    pressure_periodic := h.front.pressure_periodic
    divergence_free := ?_
    equation := localizedPair_momentum h a hβ hβs lambda
  }
  · intro t ht
    exact (LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA h ha β lambda t ht).2.1
  · intro t ht
    exact (LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA h ha β lambda t ht).2.2.1

end MethbokeAddon.FDSN
