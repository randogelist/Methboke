import FDSNResidualLocality.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff Topology

/- native_laplacian_zero. -/
example : laplacian (0 : Field) = 0 :=
  MethbokeAddon.FDSN.native_laplacian_zero

/- residualForce_eq_of_zero_germ: full correction expanded. -/
example (ν : ℝ) (U F h : Velocity) (t : ℝ) (x : Vec)
    (hh : (fun z : ℝ × Vec => h z.1 z.2) =ᶠ[𝓝 (t, x)] 0) :
    F t x + timeDerivative h t x - ν • laplacian (h t) x +
        physicalTransport (U t) (h t) x +
        physicalTransport (h t) (U t) x + convection (h t) x = F t x :=
  MethbokeAddon.FDSN.residualForce_eq_of_zero_germ ν U F h t x hh

/- velocity_zero_germ_of_notMem_timeSupport. -/
example (h : Velocity) {t : ℝ} (ht : t ∉ tsupport h) (x : Vec) :
    (fun z : ℝ × Vec => h z.1 z.2) =ᶠ[𝓝 (t, x)] 0 :=
  MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport h ht x

/- residualForce_eq_of_notMem_timeSupport. -/
example (ν : ℝ) (U F h : Velocity) {t : ℝ} (ht : t ∉ tsupport h) :
    MethbokeAddon.FDSN.residualForce ν U F h t = F t :=
  MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport ν U F h ht

/- tsupport_residualForce_sub_subset. -/
example (ν : ℝ) (U F h : Velocity) :
    tsupport (MethbokeAddon.FDSN.residualForce ν U F h - F) ⊆ tsupport h :=
  MethbokeAddon.FDSN.tsupport_residualForce_sub_subset ν U F h

/- hasCompactSupport_residualForce_sub. -/
example (ν : ℝ) (U F h : Velocity) (hh : HasCompactSupport h) :
    HasCompactSupport (MethbokeAddon.FDSN.residualForce ν U F h - F) :=
  MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub ν U F h hh

/- residualForce_eq_off_time_interval. -/
example (ν : ℝ) (U F h : Velocity) (a b : ℝ)
    (hh : tsupport h ⊆ Icc a b) {t : ℝ} (ht : t ∉ Icc a b) :
    MethbokeAddon.FDSN.residualForce ν U F h t = F t :=
  MethbokeAddon.FDSN.residualForce_eq_off_time_interval ν U F h a b hh ht

/- residualForce_positive_time_support. -/
example (ν : ℝ) (U F h : Velocity)
    (hF : ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ t : ℝ, t ∉ Icc a b → F t = 0)
    (hh : ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport h ⊆ Icc a b) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ t : ℝ, t ∉ Icc a b → MethbokeAddon.FDSN.residualForce ν U F h t = 0 :=
  MethbokeAddon.FDSN.residualForce_positive_time_support ν U F h hF hh


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_laplacian_zero"
#check @MethbokeAddon.FDSN.native_laplacian_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_laplacian_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_laplacian_zero"
#print axioms MethbokeAddon.FDSN.native_laplacian_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_laplacian_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_eq_of_zero_germ"
#check @MethbokeAddon.FDSN.residualForce_eq_of_zero_germ
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_eq_of_zero_germ"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_eq_of_zero_germ"
#print axioms MethbokeAddon.FDSN.residualForce_eq_of_zero_germ
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_eq_of_zero_germ"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport"
#check @MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport"
#print axioms MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport"
#check @MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport"
#print axioms MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.tsupport_residualForce_sub_subset"
#check @MethbokeAddon.FDSN.tsupport_residualForce_sub_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.tsupport_residualForce_sub_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.tsupport_residualForce_sub_subset"
#print axioms MethbokeAddon.FDSN.tsupport_residualForce_sub_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.tsupport_residualForce_sub_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub"
#check @MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub"
#print axioms MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.hasCompactSupport_residualForce_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_eq_off_time_interval"
#check @MethbokeAddon.FDSN.residualForce_eq_off_time_interval
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_eq_off_time_interval"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_eq_off_time_interval"
#print axioms MethbokeAddon.FDSN.residualForce_eq_off_time_interval
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_eq_off_time_interval"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_positive_time_support"
#check @MethbokeAddon.FDSN.residualForce_positive_time_support
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_positive_time_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_positive_time_support"
#print axioms MethbokeAddon.FDSN.residualForce_positive_time_support
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_positive_time_support"

