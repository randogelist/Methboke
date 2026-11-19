import EhrenfestReference.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independently stated consumer types; fresh external evidence required. -/

/-!
Exact consumer signatures and fresh axiom-audit commands for the reference helpers.
Prepared source only: none of these commands has been executed locally.
-/


open SingularClosure MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff

noncomputable section

example (s : Finset Frequency) (c : TorusSobolev 2) (i : Fin 3) :
    (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖c.val k i‖) ^ 2) ≤ ‖c‖ ^ 2 :=
  finite_component_H2_sum_le s c i

example (s : Finset Frequency) (c : TorusSobolev 2) (i : Fin 3) :
    (∑ k ∈ s, ‖c.val k i‖) ^ 2 ≤ latticeSobolevConstant * ‖c‖ ^ 2 :=
  finite_component_l1_sq_le_H2_norm_sq s c i

example (s : Finset Frequency) (c : TorusSobolev 2) (i : Fin 3) :
    (∑ k ∈ s, ‖c.val k i‖) ≤ Real.sqrt latticeSobolevConstant * ‖c‖ :=
  finite_component_l1_le_H2_norm s c i

example (k : Frequency) (x : Vec) : ‖fourierCharacter k x‖ = 1 :=
  ehrenfest_fourierCharacter_norm k x

example (N : ℕ) (c : FourierCoeff) (x : Vec) (i : Fin 3) :
    |finiteSynthesis N c x i| ≤ ∑ k ∈ cutoffModes N, ‖c k i‖ :=
  finiteSynthesis_component_abs_le_l1 N c x i

example (N : ℕ) (c : TorusSobolev 2) (x : Vec) (i : Fin 3) :
    |finiteSynthesis N c.val x i| ≤ Real.sqrt latticeSobolevConstant * ‖c‖ :=
  finiteSynthesis_component_abs_le_H2_norm N c x i

example (s : ℕ) (a : Field) (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (t : Finset FourierIndex) :
    (∑ ki ∈ t, ‖sobolevWeightedCoeff s (datumFourierCoeff a) ki‖ ^ 2) ≤
      3 * smoothDatumDecayConstant s a ^ 2 * latticeSobolevConstant :=
  smooth_datum_finite_weighted_sum_le s a ha hp t

example (s : ℕ) (a : Field) (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    ‖smoothDatumSobolev s a ha hp‖ ≤
      Real.sqrt (3 * latticeSobolevConstant) * smoothDatumDecayConstant s a :=
  smoothDatumSobolev_norm_le s a ha hp

example (s : ℕ) (a : Field) (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    ‖smoothDatumSobolev s a ha hp‖ ^ 2 ≤
      3 * smoothDatumDecayConstant s a ^ 2 * latticeSobolevConstant :=
  smoothDatumSobolev_norm_sq_le s a ha hp

example (s : ℕ) (j : Fin 3) (k : Frequency) :
    torusSobolevWeight k ^ s * ‖derivativeSymbol j k‖ ≤
      1 * torusSobolevWeight k ^ (s + 1) :=
  ehrenfest_coordinateDerivative_multiplier_bound s j k

example (s : ℕ) (j : Fin 3) : TorusSobolev (s + 1) →L[ℂ] TorusSobolev s :=
  ehrenfestTorusSobolevCoordinateDerivative s j

example (s : ℕ) (j : Fin 3) (c : TorusSobolev (s + 1)) :
    (ehrenfestTorusSobolevCoordinateDerivative s j c).val =
      spectralMultiplier (derivativeSymbol j) c.val :=
  ehrenfestTorusSobolevCoordinateDerivative_coeff s j c

example (s : ℕ) (j : Fin 3) (c : TorusSobolev (s + 1)) :
    ‖ehrenfestTorusSobolevCoordinateDerivative s j c‖ ≤ ‖c‖ :=
  ehrenfestTorusSobolevCoordinateDerivative_norm_le s j c

example (N : ℕ) (c : TorusSobolev 3) (x : Vec) (i : Fin 3) :
    |finiteSynthesis N c.val x i| ≤ Real.sqrt latticeSobolevConstant * ‖c‖ :=
  finiteSynthesis_component_abs_le_H3_norm N c x i

example (N : ℕ) (c : TorusSobolev 3) (x : Vec) (j i : Fin 3) :
    |coordinateDerivative (finiteSynthesis N c.val) j x i| ≤
      Real.sqrt latticeSobolevConstant * ‖c‖ :=
  finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm N c x j i

example (N : ℕ) (c : TorusSobolev 3) (x : Vec) :
    (∀ i : Fin 3, |finiteSynthesis N c.val x i| ≤
      Real.sqrt latticeSobolevConstant * ‖c‖) ∧
    (∀ j i : Fin 3, |coordinateDerivative (finiteSynthesis N c.val) j x i| ≤
      Real.sqrt latticeSobolevConstant * ‖c‖) :=
  finiteSynthesis_C1_components_le_H3_norm N c x


end

/-! Independently stated consumer interfaces. Prepared for external checking only. -/

open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff

noncomputable section

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (j : Fin 3) (m : ℕ) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => iteratedCoordinateDerivative j m (u z.1) z.2)
      (initialFrontSpacetime S) :=
  initial_iteratedCoordinateDerivative_contDiffOn u S hu j m

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => ∫ x in unitCube, ‖u t x i‖) (Icc (0 : ℝ) T) :=
  initial_componentL1_continuousOn_Icc u S hu i T hTS

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (j : Fin 3) (m : ℕ) (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => coordinateDerivativeL1 j m (u t) i) (Icc (0 : ℝ) T) :=
  initial_coordinateDerivativeL1_continuousOn_Icc u S hu j m i T hTS

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (m : ℕ) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => fourierDecayConstant m (u t)) (Icc (0 : ℝ) T) :=
  initial_fourierDecayConstant_continuousOn_Icc u S hu m T hTS

example (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (s : ℕ) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => smoothDatumDecayConstant s (u t)) (Icc (0 : ℝ) T) :=
  initial_smoothDatumDecayConstant_continuousOn_Icc u S hu s T hTS

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (s : ℕ) (T : ℝ) (hTS : T < S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, smoothDatumDecayConstant s (u t) ≤ C :=
  initial_front_uniform_decay_constant ν S a u p H s T hTS

example (s : ℕ) (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    TorusSobolev s :=
  initialFrontSobolev s ν S a u p H t ht

example (s : ℕ) (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    (initialFrontSobolev s ν S a u p H t ht).val = datumFourierCoeff (u t) :=
  initialFrontSobolev_coeff s ν S a u p H t ht

example (s : ℕ) (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    ∀ i : Fin 3, (initialFrontSobolev s ν S a u p H t ht).val 0 i = 0 :=
  initialFrontSobolev_meanZero s ν S a u p H t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (s : ℕ) (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      ‖initialFrontSobolev s ν S a u p H t ⟨ht.1, ht.2.trans_lt hTS⟩‖ ≤ K :=
  initial_front_uniform_sobolev_norm ν S a u p H s T hTS

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ N t (ht : t ∈ Icc (0 : ℝ) T),
      coefficientDissipation N (datumFourierCoeff (u t)) ≤ K :=
  initial_front_uniform_projected_dissipation ν S a u p H T hTS

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (T : ℝ) (hTS : T < S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N t (ht : t ∈ Icc (0 : ℝ) T) (x : Vec),
      (∀ i : Fin 3, |finiteSynthesis N (datumFourierCoeff (u t)) x i| ≤ B) ∧
      (∀ j i : Fin 3,
        |coordinateDerivative (finiteSynthesis N (datumFourierCoeff (u t))) j x i| ≤ B) :=
  initial_front_uniform_projected_C1_components ν S a u p H T hTS

example (n : ℕ) (c : TorusSobolev 2) : TorusSobolev 1 := referenceH1Tail n c

example (n : ℕ) (c : TorusSobolev 2) :
    ‖referenceH1Tail n c‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ‖c‖ :=
  referenceH1Tail_norm_le n c

example (n : ℕ) (c : TorusSobolev 2) (hc : ∀ i : Fin 3, c.val 0 i = 0) :
    (referenceH1Tail n c).val = c.val - cutoffCoeff (n + 1) c.val :=
  referenceH1Tail_coeff n c hc

example (n : ℕ) (c : TorusSobolev 2) (K : ℝ) (hK : ‖c‖ ≤ K) :
    ‖referenceH1Tail n c‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * K :=
  referenceH1Tail_norm_le_of_norm_le n c K hK

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (n : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    (referenceH1Tail n (initialFrontSobolev 2 ν S a u p H t ht)).val =
      datumFourierCoeff (u t) - cutoffCoeff (n + 1) (datumFourierCoeff (u t)) :=
  initial_front_H1_tail_coeff ν S a u p H n t ht

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p) (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n t (ht : t ∈ Icc (0 : ℝ) T),
      ‖referenceH1Tail n
        (initialFrontSobolev 2 ν S a u p H t ⟨ht.1, ht.2.trans_lt hTS⟩)‖ ≤
        ((n + 1 : ℕ) : ℝ)⁻¹ * K :=
  initial_front_uniform_H1_tail ν S a u p H T hTS


end


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_component_H2_sum_le"
#check @MethbokeAddon.EhrenfestObstruction.finite_component_H2_sum_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finite_component_H2_sum_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_component_H2_sum_le"
#print axioms MethbokeAddon.EhrenfestObstruction.finite_component_H2_sum_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finite_component_H2_sum_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_component_l1_sq_le_H2_norm_sq"
#check @MethbokeAddon.EhrenfestObstruction.finite_component_l1_sq_le_H2_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finite_component_l1_sq_le_H2_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_component_l1_sq_le_H2_norm_sq"
#print axioms MethbokeAddon.EhrenfestObstruction.finite_component_l1_sq_le_H2_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finite_component_l1_sq_le_H2_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_component_l1_le_H2_norm"
#check @MethbokeAddon.EhrenfestObstruction.finite_component_l1_le_H2_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finite_component_l1_le_H2_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_component_l1_le_H2_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.finite_component_l1_le_H2_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finite_component_l1_le_H2_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfest_fourierCharacter_norm"
#check @MethbokeAddon.EhrenfestObstruction.ehrenfest_fourierCharacter_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.ehrenfest_fourierCharacter_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfest_fourierCharacter_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.ehrenfest_fourierCharacter_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.ehrenfest_fourierCharacter_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_l1"
#check @MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_l1
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_l1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_l1"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_l1
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_l1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H2_norm"
#check @MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H2_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H2_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H2_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H2_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H2_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_datum_finite_weighted_sum_le"
#check @MethbokeAddon.EhrenfestObstruction.smooth_datum_finite_weighted_sum_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_datum_finite_weighted_sum_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_datum_finite_weighted_sum_le"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_datum_finite_weighted_sum_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_datum_finite_weighted_sum_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_le"
#check @MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_le"
#print axioms MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_sq_le"
#check @MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_sq_le"
#print axioms MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smoothDatumSobolev_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfest_coordinateDerivative_multiplier_bound"
#check @MethbokeAddon.EhrenfestObstruction.ehrenfest_coordinateDerivative_multiplier_bound
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.ehrenfest_coordinateDerivative_multiplier_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfest_coordinateDerivative_multiplier_bound"
#print axioms MethbokeAddon.EhrenfestObstruction.ehrenfest_coordinateDerivative_multiplier_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.ehrenfest_coordinateDerivative_multiplier_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative"
#check @MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative"
#print axioms MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_coeff"
#check @MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_coeff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_coeff"
#print axioms MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_norm_le"
#check @MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_norm_le"
#print axioms MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.ehrenfestTorusSobolevCoordinateDerivative_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H3_norm"
#check @MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H3_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H3_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H3_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H3_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_component_abs_le_H3_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm"
#check @MethbokeAddon.EhrenfestObstruction.finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_C1_components_le_H3_norm"
#check @MethbokeAddon.EhrenfestObstruction.finiteSynthesis_C1_components_le_H3_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_C1_components_le_H3_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_C1_components_le_H3_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteSynthesis_C1_components_le_H3_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_C1_components_le_H3_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_iteratedCoordinateDerivative_contDiffOn"
#check @MethbokeAddon.EhrenfestObstruction.initial_iteratedCoordinateDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_iteratedCoordinateDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_iteratedCoordinateDerivative_contDiffOn"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_iteratedCoordinateDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_iteratedCoordinateDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_componentL1_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_componentL1_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_componentL1_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_componentL1_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_componentL1_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_componentL1_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_coordinateDerivativeL1_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_coordinateDerivativeL1_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_coordinateDerivativeL1_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_coordinateDerivativeL1_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_coordinateDerivativeL1_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_coordinateDerivativeL1_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_fourierDecayConstant_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_fourierDecayConstant_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_fourierDecayConstant_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_fourierDecayConstant_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_fourierDecayConstant_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_fourierDecayConstant_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_smoothDatumDecayConstant_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.initial_smoothDatumDecayConstant_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_smoothDatumDecayConstant_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_smoothDatumDecayConstant_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_smoothDatumDecayConstant_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_smoothDatumDecayConstant_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_decay_constant"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_decay_constant
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_decay_constant"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_decay_constant"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_decay_constant
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_decay_constant"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev"
#check @MethbokeAddon.EhrenfestObstruction.initialFrontSobolev
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev"
#print axioms MethbokeAddon.EhrenfestObstruction.initialFrontSobolev
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_coeff"
#check @MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_coeff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_coeff"
#print axioms MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_meanZero"
#check @MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_meanZero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_meanZero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_meanZero"
#print axioms MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_meanZero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initialFrontSobolev_meanZero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_sobolev_norm"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_sobolev_norm
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_sobolev_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_sobolev_norm"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_sobolev_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_sobolev_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_dissipation"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_dissipation"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_C1_components"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_C1_components
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_C1_components"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_C1_components"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_C1_components
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_projected_C1_components"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail"
#check @MethbokeAddon.EhrenfestObstruction.referenceH1Tail
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail"
#print axioms MethbokeAddon.EhrenfestObstruction.referenceH1Tail
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le"
#check @MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le"
#print axioms MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_coeff"
#check @MethbokeAddon.EhrenfestObstruction.referenceH1Tail_coeff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_coeff"
#print axioms MethbokeAddon.EhrenfestObstruction.referenceH1Tail_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le_of_norm_le"
#check @MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le_of_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le_of_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le_of_norm_le"
#print axioms MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le_of_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.referenceH1Tail_norm_le_of_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_H1_tail_coeff"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_H1_tail_coeff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_H1_tail_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_H1_tail_coeff"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_H1_tail_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_H1_tail_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_H1_tail"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_uniform_H1_tail
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_H1_tail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_H1_tail"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_uniform_H1_tail
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_uniform_H1_tail"

