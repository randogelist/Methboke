import FDSNR3LocalizedSeed.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter SingularClosure
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

example (χ : ℝ → ℝ) (u : Velocity) (t : ℝ) (x : Vec) :
    localizedSeed χ u t x = χ t • u t x := rfl

example (χ : ℝ → ℝ) (u : Velocity) {t : ℝ} (ht : t ∉ tsupport χ) :
    localizedSeed χ u t = 0 := by
  apply MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support <;> assumption

example (χ : ℝ → ℝ) (u : Velocity) {t : ℝ} (ht : t ∉ tsupport χ) (x : Vec) :
    (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun _ => (0 : Vec)) := by
  apply MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support <;> assumption

example (χ : ℝ → ℝ) (u : Velocity) (n : ℕ) {t : ℝ}
    (ht : t ∉ tsupport χ) (x : Vec) :
    iteratedFDeriv ℝ n (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) (t, x) = 0 := by
  apply MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support <;> assumption

example {χ : ℝ → ℝ} (u : Velocity) {t : ℝ} (ht : χ t = 1) :
    localizedSeed χ u t = u t := by
  apply MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one <;> assumption

example {χ : ℝ → ℝ} (u : Velocity) {t : ℝ}
    (ht : χ =ᶠ[𝓝 t] (fun _ => (1 : ℝ))) (x : Vec) :
    (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z : ℝ × Vec => u z.1 z.2) := by
  apply MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one <;> assumption

example {χ : ℝ → ℝ} (u : Velocity) {t : ℝ}
    (ht : χ =ᶠ[𝓝 t] (fun _ => (1 : ℝ))) (x : Vec) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) (t, x) =
      iteratedFDeriv ℝ n (fun z : ℝ × Vec => u z.1 z.2) (t, x) := by
  apply MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one <;> assumption

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hsupport : tsupport χ ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed <;> assumption

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsupport : tsupport χ ⊆ Ioo (0 : ℝ) T) :
    Function.HasTemperateGrowth (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed <;> assumption

example {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo (0 : ℝ) T ∧
      ∀ t ∈ Icc a b, χ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
  apply MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval <;> assumption

end

end MethbokeAddon.FDSNR3

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed"
#check @MethbokeAddon.FDSNR3.localizedSeed
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed"
#print axioms MethbokeAddon.FDSNR3.localizedSeed
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support"
#check @MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support"
#print axioms MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed_eq_zero_off_support"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support"
#check @MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support"
#print axioms MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_zero_off_support"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support"
#check @MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support"
#print axioms MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_zero_off_support"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one"
#check @MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one"
#print axioms MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed_eq_of_eq_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one"
#check @MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one"
#print axioms MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed_eventuallyEq_of_eventuallyEq_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one"
#check @MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one"
#print axioms MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiff_localizedSeed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasTemperateGrowth_localizedSeed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval"
#check @MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval"
#print axioms MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.exists_timeCutoff_for_interval"

