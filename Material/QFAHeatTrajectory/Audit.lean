import QFAHeatTrajectory.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal Topology

namespace QFAHeatTrajectory.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatSmoothing
open MethbokeAddon.QuasiFeffermanA.HeatTrajectory

example : (ν : ℝ≥0) → 0 < ν → PhysicalH1 → ℝ → PhysicalH2 := heatTrajectory
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (t : ℝ) :
    heatTrajectory ν hν u t =
      if ht : 0 < t then heatH1ToH2 ν t.toNNReal hν (Real.toNNReal_pos.mpr ht) u else 0 := rfl
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    heatTrajectory ν hν u t = heatH1ToH2 ν t.toNNReal hν (Real.toNNReal_pos.mpr ht) u :=
  heatTrajectory_eq_of_pos ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : t ≤ 0) :
    heatTrajectory ν hν u t = 0 := heatTrajectory_eq_zero_of_nonpos ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    physicalH2Velocity (heatTrajectory ν hν u t) = heatL2 ν t.toNNReal (physicalH1Velocity u) :=
  heatTrajectory_velocity ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    physicalH2ToH1 (heatTrajectory ν hν u t) = heatH1 ν t.toNNReal u :=
  heatTrajectory_toH1 ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (s : ℝ≥0) (hs : 0 < s)
    {t : ℝ} (hst : (s : ℝ) < t) :
    heatTrajectory ν hν u t = heatH1ToH2CLM ν s hν hs (heatH1 ν (t - (s : ℝ)).toNNReal u) :=
  heatTrajectory_factor ν hν u s hs hst
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (heatTrajectory ν hν u) t := heatTrajectory_continuousAt_pos ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : t < 0) :
    ContinuousAt (heatTrajectory ν hν u) t := heatTrajectory_continuousAt_neg ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) :
    ContinuousOn (heatTrajectory ν hν u) (Set.Ioi (0 : ℝ)) :=
  heatTrajectory_continuousOn_pos ν hν u
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) :
    ContinuousOn (heatTrajectory ν hν u) ({0}ᶜ : Set ℝ) :=
  heatTrajectory_continuousOn_ne_zero ν hν u
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) :
    StronglyMeasurable (heatTrajectory ν hν u) := heatTrajectory_stronglyMeasurable ν hν u
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) :
    StronglyMeasurable (fun t : ℝ => physicalH2Laplacian (heatTrajectory ν hν u t)) :=
  heatTrajectory_laplacian_stronglyMeasurable ν hν u
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) :
    StronglyMeasurable (fun t : ℝ => ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) :=
  heatTrajectory_laplacian_sq_stronglyMeasurable ν hν u
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    ‖heatTrajectory ν hν u t‖ ^ 2 = ‖heatH1 ν t.toNNReal u‖ ^ 2 +
      ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 :=
  heatTrajectory_norm_sq ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (t : ℝ) :
    ‖heatTrajectory ν hν u t‖ ^ 2 ≤ ‖u‖ ^ 2 +
      ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 :=
  heatTrajectory_norm_sq_le ν hν u t

-- Literal finite-window consequence: measurability is proved for the actual
-- H2 path with no assumed measurable representative or integrability field.
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) :
    AEStronglyMeasurable (heatTrajectory ν hν u)
      (volume.restrict (Set.Ioo (0 : ℝ) T)) :=
  (heatTrajectory_stronglyMeasurable ν hν u).aestronglyMeasurable

end QFAHeatTrajectory.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_of_pos"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_of_pos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_of_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_of_pos"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_of_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_of_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_zero_of_nonpos"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_zero_of_nonpos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_zero_of_nonpos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_zero_of_nonpos"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_zero_of_nonpos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_eq_zero_of_nonpos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_velocity"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_toH1"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_toH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_toH1"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_factor"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_factor
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_factor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_factor"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_factor
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_factor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_pos"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_pos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_pos"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_neg"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_neg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_neg"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousAt_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_pos"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_pos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_pos"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_ne_zero"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_ne_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_continuousOn_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_stronglyMeasurable"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_stronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_stronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_stronglyMeasurable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_stronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_stronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_stronglyMeasurable"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_stronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_stronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_stronglyMeasurable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_stronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_stronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_sq_stronglyMeasurable"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_sq_stronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_sq_stronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_sq_stronglyMeasurable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_sq_stronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_laplacian_sq_stronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq_le"
#check MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTrajectory.heatTrajectory_norm_sq_le"
