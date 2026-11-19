import EhrenfestReferenceEvolution.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.EhrenfestObstruction
open scoped ContDiff

example (S : ℝ) (F D : ℝ → Vec → ℂ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime S))
    (hD : ContinuousOn (fun z : ℝ × Vec => D z.1 z.2) (localFrontSpacetime S))
    (hd : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Vec, HasDerivAt (fun r => F r x) (D t x) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => ∫ x in unitCube, F r x) (∫ x in unitCube, D t x) t :=
  local_hasDerivAt_complex_cube_integral S F D hF hD hd t ht

example (S : ℝ) (F : ℝ → Vec → ℂ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (initialFrontSpacetime S))
    (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun r => ∫ x in unitCube, F r x) (Icc (0 : ℝ) T) :=
  initial_complex_cube_integral_continuousOn_Icc S F hF T hTS

example (u : Velocity) (s : Set (ℝ × Vec))
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) s)
    (k : Frequency) (i : Fin 3) :
    ContinuousOn (fun z : ℝ × Vec => datumFourierIntegrand (u z.1) k i z.2) s :=
  datumFourierIntegrand_continuousOn_spacetime u s hu k i

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime S))
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) t :=
  local_datumFourierCoeff_hasDerivAt u S hu k i t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) t :=
  initial_front_datumFourierCoeff_hasDerivAt ν S a u p H k i t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => datumFourierCoeff (u t) k i) (Icc (0 : ℝ) T) :=
  initial_front_datumFourierCoeff_continuousOn_Icc ν S a u p H k i T hTS

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    SpectralSolenoidal (datumFourierCoeff (timeDerivative u t)) :=
  initial_front_timeDerivative_fourier_solenoidal ν S a u p H t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) (k : Frequency) :
    coefficientLeray k (datumFourierCoeff (timeDerivative u t) k) =
      datumFourierCoeff (timeDerivative u t) k :=
  initial_front_timeDerivative_fourier_leray ν S a u p H t ht k
end Consumer1

section Consumer2
open MethbokeAddon.WeakFouriermanB
/-! Prepared consumer checks and axiom-audit commands; not executed locally. -/


open Set MeasureTheory SingularClosure
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff

noncomputable section

example (c : TorusSobolev 0) (i : Fin 3) :
    (∑' k : Frequency, ‖c.val k i‖ ^ 2) ≤ ‖c‖ ^ 2 :=
  torusSobolev_H0_component_tsum_norm_sq_le c i

example (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    (∫ x in unitCube, (v x i) ^ 2) =
      ∑' k : Frequency, ‖datumFourierCoeff v k i‖ ^ 2 :=
  smooth_periodic_component_parseval v hv hp i

example (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 0) (hc : c.val = datumFourierCoeff v) :
    physicalEnergy v ≤ 3 * ‖c‖ ^ 2 :=
  smooth_periodic_physicalEnergy_le_H0_norm_sq v hv hp c hc

example (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 1) (hc : c.val = datumFourierCoeff v) :
    physicalEnergy v ≤ 3 * ‖c‖ ^ 2 :=
  smooth_periodic_physicalEnergy_le_H1_norm_sq v hv hp c hc

example (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 1) (hc : c.val = datumFourierCoeff v) :
    physicalDissipation v ≤ 9 * ‖c‖ ^ 2 :=
  smooth_periodic_physicalDissipation_le_H1_norm_sq v hv hp c hc

example (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 1) (hc : c.val = datumFourierCoeff v) :
    (∫ x in unitCube, ‖v x‖ ^ 2) + physicalDissipation v ≤ 12 * ‖c‖ ^ 2 :=
  smooth_periodic_physical_H1_le_torusSobolev v hv hp c hc

example (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a - b) = datumFourierCoeff a - datumFourierCoeff b :=
  ehrenfest_datumFourierCoeff_sub a b ha hb

example (N : ℕ) (v : Field) : Field := physicalReferenceTail N v

example (N : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (physicalReferenceTail N v) :=
  physicalReferenceTail_smooth N v hv

example (N : ℕ) (v : Field) (hp : SpatialPeriodic v) :
    SpatialPeriodic (physicalReferenceTail N v) :=
  physicalReferenceTail_periodic N v hp

example (N : ℕ) (v : Field) (hv : Continuous v) :
    datumFourierCoeff (physicalReferenceTail N v) =
      datumFourierCoeff v - cutoffCoeff N (datumFourierCoeff v) :=
  physicalReferenceTail_coeff N v hv

example (n : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 2) (hc : c.val = datumFourierCoeff v)
    (hz : ∀ i : Fin 3, c.val 0 i = 0) :
    (∫ x in unitCube, ‖physicalReferenceTail (n + 1) v x‖ ^ 2) +
      physicalDissipation (physicalReferenceTail (n + 1) v) ≤
        12 * ‖referenceH1Tail n c‖ ^ 2 :=
  physicalReferenceTail_physical_H1_le n v hv hp c hc hz

example (n : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 2) (hc : c.val = datumFourierCoeff v)
    (hz : ∀ i : Fin 3, c.val 0 i = 0) :
    (∫ x in unitCube, ‖physicalReferenceTail (n + 1) v x‖ ^ 2) +
      physicalDissipation (physicalReferenceTail (n + 1) v) ≤
        12 * (((n + 1 : ℕ) : ℝ)⁻¹ * ‖c‖) ^ 2 :=
  physicalReferenceTail_physical_H1_le_rate n v hv hp c hc hz

example (n : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hz : SpectralMeanZero (datumFourierCoeff v)) :
    (∫ x in unitCube, ‖physicalReferenceTail (n + 1) v x‖ ^ 2) +
      physicalDissipation (physicalReferenceTail (n + 1) v) ≤
        12 * (((n + 1 : ℕ) : ℝ)⁻¹ * ‖smoothDatumSobolev 2 v hv hp‖) ^ 2 :=
  smoothDatum_physicalReferenceTail_physical_H1_le_rate n v hv hp hz

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n t (ht : t ∈ Icc (0 : ℝ) T),
      (∫ x in unitCube, ‖physicalReferenceTail (n + 1) (u t) x‖ ^ 2) +
        physicalDissipation (physicalReferenceTail (n + 1) (u t)) ≤
          12 * (((n + 1 : ℕ) : ℝ)⁻¹ * K) ^ 2 :=
  initial_front_uniform_physical_H1_tail ν S a u p H T hTS


end
end Consumer2

section Consumer3
open Set SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.EhrenfestObstruction

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    datumFourierCoeff (timeDerivative u t) k i =
      -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
          datumFourierCoeff (u t) k i -
        coefficientLeray k (datumFourierCoeff (convection (u t)) k) i :=
  initial_front_projected_fourier_rhs ν S a u p H k i t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
          datumFourierCoeff (u t) k i -
        coefficientLeray k (datumFourierCoeff (convection (u t)) k) i) t :=
  initial_front_projected_fourier_hasDerivAt ν S a u p H k i t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (N : ℕ) (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => cutoffCoeff N (datumFourierCoeff (u r)) k i)
      (cutoffCoeff N (fun q j =>
        -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq q : ℝ) : ℝ) : ℂ) *
            datumFourierCoeff (u t) q j -
          coefficientLeray q (datumFourierCoeff (convection (u t)) q) j) k i) t :=
  initial_front_cutoff_fourier_hasDerivAt ν S a u p H N k i t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (N : ℕ) (k : Frequency) (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => cutoffCoeff N (datumFourierCoeff (u t)) k i)
      (Icc (0 : ℝ) T) :=
  initial_front_cutoff_fourier_continuousOn_Icc ν S a u p H N k i T hTS
end Consumer3

section Consumer4
/-! Prepared exact consumer checks and fresh axiom-audit commands; not locally run. -/


open Set SingularClosure MethbokeAddon.WeakFouriermanB
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff

noncomputable section

example (v : Vec) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i : Fin 3, |v i| ≤ B) :
    ‖v‖ ≤ 2 * B :=
  vec_norm_le_two_mul_of_component_abs_le v B hB h

example (v : Field) (x : Vec) :
    ‖fderiv ℝ v x‖ ≤ ∑ j : Fin 3, ‖coordinateDerivative v j x‖ :=
  fderiv_norm_le_sum_coordinate_norm v x

example (v : Field) (x : Vec) (B : ℝ)
    (h : ∀ j : Fin 3, ‖coordinateDerivative v j x‖ ≤ B) :
    ‖fderiv ℝ v x‖ ≤ 3 * B :=
  fderiv_norm_le_three_mul_of_coordinate_norm_le v x B h

example (v : Field) (x : Vec) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ j i : Fin 3, |coordinateDerivative v j x i| ≤ B) :
    ‖fderiv ℝ v x‖ ≤ 6 * B :=
  fderiv_norm_le_six_mul_of_component_abs_le v x B hB h

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S)) (T : ℝ) (hTS : T < S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t (ht : t ∈ Icc (0 : ℝ) T) (x : Vec)
      (hx : x ∈ unitCube), ‖fderiv ℝ (u t) x‖ ≤ C :=
  initial_joint_smooth_uniform_fderiv_norm u S hu T hTS

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (T : ℝ) (hTS : T < S) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ N t (ht : t ∈ Icc (0 : ℝ) T) (x : Vec)
      (hx : x ∈ unitCube),
      ‖finiteSynthesis N (datumFourierCoeff (u t)) x‖ ≤ M ∧
      ‖fderiv ℝ (finiteSynthesis N (datumFourierCoeff (u t))) x‖ ≤ M ∧
      ‖fderiv ℝ (u t) x‖ ≤ M :=
  initial_front_uniform_C1_norms ν S a u p H T hTS


end
end Consumer4


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.local_hasDerivAt_complex_cube_integral"
#check @MethbokeAddon.EhrenfestObstruction.local_hasDerivAt_complex_cube_integral
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.local_hasDerivAt_complex_cube_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.local_hasDerivAt_complex_cube_integral"
#print axioms MethbokeAddon.EhrenfestObstruction.local_hasDerivAt_complex_cube_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.local_hasDerivAt_complex_cube_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_complex_cube_integral_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_complex_cube_integral_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_complex_cube_integral_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_complex_cube_integral_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_complex_cube_integral_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_complex_cube_integral_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierIntegrand_continuousOn_spacetime"
#check @MethbokeAddon.EhrenfestObstruction.datumFourierIntegrand_continuousOn_spacetime
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.datumFourierIntegrand_continuousOn_spacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierIntegrand_continuousOn_spacetime"
#print axioms MethbokeAddon.EhrenfestObstruction.datumFourierIntegrand_continuousOn_spacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.datumFourierIntegrand_continuousOn_spacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.local_datumFourierCoeff_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.local_datumFourierCoeff_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.local_datumFourierCoeff_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.local_datumFourierCoeff_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.local_datumFourierCoeff_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.local_datumFourierCoeff_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_datumFourierCoeff_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_solenoidal"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_solenoidal"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_leray"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_leray
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_leray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_leray"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_leray
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_timeDerivative_fourier_leray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.torusSobolev_H0_component_tsum_norm_sq_le"
#check @MethbokeAddon.EhrenfestObstruction.torusSobolev_H0_component_tsum_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.torusSobolev_H0_component_tsum_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.torusSobolev_H0_component_tsum_norm_sq_le"
#print axioms MethbokeAddon.EhrenfestObstruction.torusSobolev_H0_component_tsum_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.torusSobolev_H0_component_tsum_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_component_parseval"
#check @MethbokeAddon.EhrenfestObstruction.smooth_periodic_component_parseval
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_component_parseval"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_component_parseval"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_periodic_component_parseval
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_component_parseval"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H0_norm_sq"
#check @MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H0_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H0_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H0_norm_sq"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H0_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H0_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H1_norm_sq"
#check @MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H1_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H1_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H1_norm_sq"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H1_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalEnergy_le_H1_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalDissipation_le_H1_norm_sq"
#check @MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalDissipation_le_H1_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalDissipation_le_H1_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalDissipation_le_H1_norm_sq"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalDissipation_le_H1_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physicalDissipation_le_H1_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physical_H1_le_torusSobolev"
#check @MethbokeAddon.EhrenfestObstruction.smooth_periodic_physical_H1_le_torusSobolev
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physical_H1_le_torusSobolev"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physical_H1_le_torusSobolev"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_periodic_physical_H1_le_torusSobolev
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_periodic_physical_H1_le_torusSobolev"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfest_datumFourierCoeff_sub"
#check @MethbokeAddon.EhrenfestObstruction.ehrenfest_datumFourierCoeff_sub
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.ehrenfest_datumFourierCoeff_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfest_datumFourierCoeff_sub"
#print axioms MethbokeAddon.EhrenfestObstruction.ehrenfest_datumFourierCoeff_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.ehrenfest_datumFourierCoeff_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceTail
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceTail
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_smooth"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_smooth
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_smooth"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_periodic"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_periodic
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_periodic"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_coeff"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_coeff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_coeff"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le_rate"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le_rate
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le_rate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le_rate"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le_rate
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceTail_physical_H1_le_rate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smoothDatum_physicalReferenceTail_physical_H1_le_rate"
#check @MethbokeAddon.EhrenfestObstruction.smoothDatum_physicalReferenceTail_physical_H1_le_rate
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smoothDatum_physicalReferenceTail_physical_H1_le_rate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smoothDatum_physicalReferenceTail_physical_H1_le_rate"
#print axioms MethbokeAddon.EhrenfestObstruction.smoothDatum_physicalReferenceTail_physical_H1_le_rate
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smoothDatum_physicalReferenceTail_physical_H1_le_rate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_physical_H1_tail"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_physical_H1_tail
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_physical_H1_tail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_physical_H1_tail"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_physical_H1_tail
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_physical_H1_tail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_rhs"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_rhs
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_rhs"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_rhs"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_rhs
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_rhs"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_projected_fourier_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_cutoff_fourier_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.vec_norm_le_two_mul_of_component_abs_le"
#check @MethbokeAddon.EhrenfestObstruction.vec_norm_le_two_mul_of_component_abs_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.vec_norm_le_two_mul_of_component_abs_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.vec_norm_le_two_mul_of_component_abs_le"
#print axioms MethbokeAddon.EhrenfestObstruction.vec_norm_le_two_mul_of_component_abs_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.vec_norm_le_two_mul_of_component_abs_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_sum_coordinate_norm"
#check @MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_sum_coordinate_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_sum_coordinate_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_sum_coordinate_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_sum_coordinate_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_sum_coordinate_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_three_mul_of_coordinate_norm_le"
#check @MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_three_mul_of_coordinate_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_three_mul_of_coordinate_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_three_mul_of_coordinate_norm_le"
#print axioms MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_three_mul_of_coordinate_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_three_mul_of_coordinate_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_six_mul_of_component_abs_le"
#check @MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_six_mul_of_component_abs_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_six_mul_of_component_abs_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_six_mul_of_component_abs_le"
#print axioms MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_six_mul_of_component_abs_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.fderiv_norm_le_six_mul_of_component_abs_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_joint_smooth_uniform_fderiv_norm"
#check @MethbokeAddon.EhrenfestObstruction.initial_joint_smooth_uniform_fderiv_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_joint_smooth_uniform_fderiv_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_joint_smooth_uniform_fderiv_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_joint_smooth_uniform_fderiv_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_joint_smooth_uniform_fderiv_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_C1_norms"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_C1_norms
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_C1_norms"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_C1_norms"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_C1_norms
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_C1_norms"
