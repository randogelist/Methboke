import QFAHeatSpatialEnergy.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy
open scoped BigOperators

noncomputable section

example (u v : PhysicalH1) (j : Fin 3) :
    inner ℝ (physicalH1Velocity u) (physicalH1Gradient j v) =
      -inner ℝ (physicalH1Gradient j u) (physicalH1Velocity v) :=
  physicalH1_gradient_integration_by_parts u v j

example (u : PhysicalH1) (v : PhysicalH2) :
    inner ℝ (physicalH1Velocity u) (physicalH2Laplacian v) =
      -(∑ j : Fin 3, inner ℝ (physicalH1Gradient j u) (physicalH2Gradient j v)) :=
  physicalH1H2_laplacian_pairing u v

example (u v : PhysicalH2) :
    inner ℝ (physicalH2Laplacian u) (physicalH2Velocity v) =
      inner ℝ (physicalH2Velocity u) (physicalH2Laplacian v) :=
  physicalH2_laplacian_symmetric u v

/- Expand enstrophy into the literal actual three-gradient squared norms. -/
example (u : PhysicalH2) :
    inner ℝ (physicalH2Velocity u) (physicalH2Laplacian u) =
      -(∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) := by
  simpa only [physicalH1Enstrophy, physicalH2ToH1_gradient] using
    physicalH2_laplacian_enstrophy u

/- Multiplying the physical Laplacian preserves the exact coefficient,
with no hidden factor one-half or doubled dissipation. -/
example (ν : ℝ) (u : PhysicalH2) :
    inner ℝ (physicalH2Velocity u) (ν • physicalH2Laplacian u) =
      -(ν * ∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) := by
  rw [inner_smul_right, physicalH2_laplacian_enstrophy]
  simp only [physicalH1Enstrophy, physicalH2ToH1_gradient]
  ring

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts"
#check @MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing"
#check @MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric"
#check @MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy"
#check @MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy"

