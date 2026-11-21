import MethbokeAddon.QuasiFeffermanA.LHRestart
import MethbokeAddon.QuasiFeffermanA.PhysicalH1

/-!
# Exact physical H1 packaging of the selected QFA restart

This endpoint packages the already constructed safe full restart into the
native complete `PhysicalH1Sigma` carrier.  The datum uses the original
velocity trace `u s` and the original supplied weak-gradient witness `G s`.
It introduces no solution constructor, Sobolev estimate, continuation,
comparison, smoothness, or global QFA conclusion.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Topology

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Representation QFA.Endpoints.Restart

/-- Package one exact solenoidal weak-gradient pair as native physical H1_sigma. -/
def physicalH1SigmaOfWeakGradient
    (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hgrad : SpatialWeakGradient v G) (hsol : Solenoidal v) : PhysicalH1Sigma :=
  ⟨h1Pack v G, (mem_physicalH1SigmaGraph_iff _).mpr ⟨hgrad, hsol⟩⟩

@[simp] theorem physicalH1SigmaOfWeakGradient_velocity
    (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hgrad : SpatialWeakGradient v G) (hsol : Solenoidal v) :
    (physicalH1SigmaOfWeakGradient v G hgrad hsol).val 0 = v := rfl

@[simp] theorem physicalH1SigmaOfWeakGradient_gradient
    (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hgrad : SpatialWeakGradient v G) (hsol : Solenoidal v) (j : Fin 3) :
    (physicalH1SigmaOfWeakGradient v G hgrad hsol).val j.succ = G j := rfl

/-- The complete selected-restart object consumed by the later strong-reference
construction.  Every field refers to the same original path and time. -/
structure SafeH1Restart (S ν : ℝ) (a : SpatialL2)
    (u : Velocity) (G : WeakGradient) where
  time : ℝ
  time_pos : 0 < time
  time_lt_cutoff : time < safeCutoff S ‖a‖ ν
  datum : PhysicalH1Sigma
  datum_velocity : datum.val 0 = u time
  datum_gradient : ∀ j : Fin 3, datum.val j.succ = G time j
  energy_start : EnergyStart ν u G time
  restart_data : QFA.Assembly.Restart.RestartData ν u G time
  shifted_leray_hopf :
    LerayHopf ν (u time)
      (QFA.Endpoints.Restart.timeTranslate time u)
      (QFA.Endpoints.Restart.timeTranslate time G)
  right_trace : Tendsto u (𝓝[>] time) (𝓝 (u time))
  small_product :
    velocityEnergy (u time) * gradientEnergy (G time) < productThreshold S ν

/-- The packaged datum has exactly the physical velocity-plus-gradient norm. -/
theorem SafeH1Restart.datum_norm_sq
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (r : SafeH1Restart S ν a u G) :
    ‖r.datum‖ ^ 2 =
      velocityEnergy (u r.time) + gradientEnergy (G r.time) := by
  rw [physicalH1Sigma_norm_sq, r.datum_velocity]
  simp only [velocityEnergy, gradientEnergy, r.datum_gradient]

/-- The strict selected product is literally the product of the packaged
physical H1 datum's velocity and gradient projections. -/
theorem SafeH1Restart.datum_small_product
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (r : SafeH1Restart S ν a u G) :
    velocityEnergy (r.datum.val 0) *
        gradientEnergy (fun j : Fin 3 => r.datum.val j.succ) <
      productThreshold S ν := by
  have hgrad : (fun j : Fin 3 => r.datum.val j.succ) = G r.time := by
    funext j
    exact r.datum_gradient j
  rw [r.datum_velocity, hgrad]
  exact r.small_product

/-- The accepted safe full restart yields one exact native H1_sigma datum,
without changing the selected trace or its gradient witness. -/
theorem LerayHopf.exists_safe_h1_restart
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    Nonempty (SafeH1Restart S ν a u G) := by
  obtain ⟨s, hs0, hsR, hsol, hgrad, hstart, hdata, hshift, htrace, hsmall⟩ :=
    h.exists_safe_full_restart hS hν ha
  let b : PhysicalH1Sigma :=
    physicalH1SigmaOfWeakGradient (u s) (G s) hgrad hsol
  refine ⟨{
    time := s
    time_pos := hs0
    time_lt_cutoff := hsR
    datum := b
    datum_velocity := ?_
    datum_gradient := ?_
    energy_start := hstart
    restart_data := hdata
    shifted_leray_hopf := hshift
    right_trace := htrace
    small_product := hsmall
  }⟩
  · rfl
  · intro j
    rfl

end MethbokeAddon.QuasiFeffermanA
