import WFBLocalFrontIdentification.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (τ : ℝ) (hτ0 : 0 < τ) (hτT : τ < T)
    (hSerrin : MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ))),
    ∀ r ∈ Ioc (0 : ℝ) τ, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hSerrin : ∀ τ : ℝ, 0 < τ → τ < T →
      MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
        (volume.restrict (Ioc (0 : ℝ) τ))),
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hSerrin : MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioo (0 : ℝ) T))),
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hbudget : FourierBudgetFinite (fun r => datumFourierCoeff (u r)) T),
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun r => datumFourierCoeff (u r)) T),
    ∃ (v : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) v G ∧
      v 0 =ᵐ[volume.restrict unitCube] a ∧
      ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on"
#check @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_on"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin"
#check @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_compact_serrin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin"
#check @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_serrin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_leray_hopf_identification_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_original_leray_hopf_of_fourier_budget"

