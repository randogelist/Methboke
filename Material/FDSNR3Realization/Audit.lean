import FDSNR3Realization.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff SchwartzMap Topology
open LineDeriv

noncomputable section

example (N n : ℕ) (u v : Velocity)
    (hu : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2))
    (hv : ContDiff ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2)) (z : ℝ × Vec) :
    weightedJet N n (u + v) z ≤ weightedJet N n u z + weightedJet N n v z := by
  apply MethbokeAddon.FDSNR3.weightedJet_add_le <;> assumption

example {u v : Velocity}
    (hu : GlobalSchwartzBounds u) (hv : GlobalSchwartzBounds v)
    (hus : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2))
    (hvs : ContDiff ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2)) :
    GlobalSchwartzBounds (u + v) := by
  apply MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add <;> assumption

example {T : ℝ} {v : Velocity}
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2))
    (hb : GlobalSchwartzBounds v) : LocalSchwartz T v := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.of_global <;> assumption

example {T : ℝ} {u v : Velocity}
    (hu : LocalSchwartz T u) (hv : LocalSchwartz T v) :
    LocalSchwartz T (u + v) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.add <;> assumption

example {T : ℝ} {u h : Velocity}
    (hu : LocalSchwartz T u)
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2))
    (hb : GlobalSchwartzBounds h) : LocalSchwartz T (u + h) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.add_global <;> assumption

example {F G : Velocity}
    (hF : AdmissibleForce F) (hG : AdmissibleForce G) : AdmissibleForce (F + G) := by
  apply MethbokeAddon.FDSNR3.AdmissibleForce.add <;> assumption

example {a b : ℝ} {h : Velocity}
    (hh : CompactTemporalCorrection a b h) (ha : 0 < a) (hab : a < b) :
    AdmissibleForce h := by
  apply MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce <;> assumption

example {ν T : ℝ} {u h F : Velocity} {p : Pressure}
    (hu : PreterminalNSE ν T u p F)
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2))
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (h t) x = 0) :
    PreterminalNSE ν T (u + h) p (MethbokeAddon.FDSN.residualForce ν u F h) := by
  apply MethbokeAddon.FDSNR3.PreterminalNSE.add_residual <;> assumption

example (ν : ℝ) (u F h : Velocity) :
    MethbokeAddon.FDSN.residualForce ν u F h =
      F + MethbokeAddon.FDSN.residualForce ν u 0 h := by
  apply MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force <;> assumption

example {ν a b : ℝ} {u F h : Velocity} (hF : AdmissibleForce F)
    (hcorrection : CompactTemporalCorrection a b
      (MethbokeAddon.FDSN.residualForce ν u 0 h))
    (ha : 0 < a) (hab : a < b) :
    AdmissibleForce (MethbokeAddon.FDSN.residualForce ν u F h) := by
  apply MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction <;> assumption

example {T : ℝ} {u v : Velocity}
    (hu : BoundedEnergy T u)
    (hv : ∀ t ∈ Ico (0 : ℝ) T, Integrable (fun x : Vec => ‖v t x‖ ^ 2) volume)
    (heq : ∀ t ∈ Ico (0 : ℝ) T,
      (∫ x : Vec, ‖v t x‖ ^ 2) = ∫ x : Vec, ‖u t x‖ ^ 2) :
    BoundedEnergy T v := by
  apply MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history <;> assumption

example {T : ℝ} {u v : Velocity}
    (hu : FiniteDissipation T u)
    (hv : ∀ t ∈ Ico (0 : ℝ) T, Integrable (gradientSquare (v t)) volume)
    (heq : ∀ t ∈ Ico (0 : ℝ) T, dissipation (v t) = dissipation (u t)) :
    FiniteDissipation T v := by
  apply MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history <;> assumption

example {T ε : ℝ} {u : Velocity} {U : ℝ → Velocity}
    (h : EnergyDissipationPreservation T ε u U)
    {lam : ℝ} (hlam : |lam| < ε) :
    (∫ t in Ioo (0 : ℝ) T, dissipation (U lam t)) =
      ∫ t in Ioo (0 : ℝ) T, dissipation (u t) :=
  MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation h hlam

example {T ε : ℝ} {u : Velocity} {U : ℝ → Velocity}
    (h : EnergyDissipationPreservation T ε u U)
    {lam : ℝ} (hlam : |lam| < ε) :
    (∫ t in Ioo (0 : ℝ) T, ∫ x : Vec,
      ∑ i : Fin 3, ‖coordinateDerivative (U lam t) i x‖ ^ 2) =
    (∫ t in Ioo (0 : ℝ) T, ∫ x : Vec,
      ∑ i : Fin 3, ‖coordinateDerivative (u t) i x‖ ^ 2) := by
  simpa only [dissipation, gradientSquare] using
    MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation h hlam

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedJet_add_le"
#check @MethbokeAddon.FDSNR3.weightedJet_add_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedJet_add_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedJet_add_le"
#print axioms MethbokeAddon.FDSNR3.weightedJet_add_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedJet_add_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add"
#check @MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add"
#print axioms MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.GlobalSchwartzBounds.add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.of_global"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.of_global
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.of_global"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.of_global"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.of_global
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.of_global"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.add"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.add"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.add_global"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.add_global
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.add_global"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.add_global"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.add_global
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.add_global"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.AdmissibleForce.add"
#check @MethbokeAddon.FDSNR3.AdmissibleForce.add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.AdmissibleForce.add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.AdmissibleForce.add"
#print axioms MethbokeAddon.FDSNR3.AdmissibleForce.add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.AdmissibleForce.add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce"
#check @MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce"
#print axioms MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CompactTemporalCorrection.admissibleForce"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.PreterminalNSE.add_residual"
#check @MethbokeAddon.FDSNR3.PreterminalNSE.add_residual
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.PreterminalNSE.add_residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.PreterminalNSE.add_residual"
#print axioms MethbokeAddon.FDSNR3.PreterminalNSE.add_residual
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.PreterminalNSE.add_residual"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force"
#check @MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force"
#print axioms MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.residualForce_eq_add_zero_force"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction"
#check @MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction"
#print axioms MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.admissibleForce_residual_of_correction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history"
#check @MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history"
#print axioms MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.BoundedEnergy.of_equal_history"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history"
#check @MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history"
#print axioms MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.FiniteDissipation.of_equal_history"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation"
#check @MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation"
#print axioms MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.EnergyDissipationPreservation.integrated_dissipation"

