import WFBPhysicalEnstrophyEvolution.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology RealInnerProductSpace
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn
example : ∀ (T : ℝ),
    UniqueDiffOn ℝ (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Vec) (j : Fin 3),
    coordinateDerivative (u t) j x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (initialFrontSpacetime T) (t, x) (0, unitVector j) :=
  @MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (j : Fin 3),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T)),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => laplacian (u z.1) z.2)
      (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T)),
    ContinuousOn (fun z : ℝ × Vec => convection (u z.1) z.2) (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T),
    ContinuousOn (fun t => physicalDissipation (u t)) (Icc (0 : ℝ) τ) :=
  @MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T),
    ContinuousOn (fun t => physicalLaplacianSquare (u t)) (Icc (0 : ℝ) τ) :=
  @MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (j : Fin 3),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      (localFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => timeDerivative u z.1 z.2)
      (localFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (j : Fin 3) (x : Vec),
    timeDerivative (fun r => coordinateDerivative (u r) j) t x =
      coordinateDerivative (timeDerivative u t) j x :=
  @MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic
example : ∀ (u : Velocity) (T : ℝ)
    (hp : ∀ r ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u r))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    SpatialPeriodic (timeDerivative u t) :=
  @MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt
example : ∀ (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (hp : ∀ r ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u r))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    HasDerivAt (fun r => physicalDissipation (u r))
      (-2 * physicalFieldInner (timeDerivative u t) (laplacian (u t))) t :=
  @MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free
example : ∀ (v : Field) (hv : SmoothSigmaZero v) (x : Vec),
    divergence (laplacian v) x = 0 :=
  @MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc
example : ∀ (ν : ℝ) (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T),
    ContinuousOn (fun t => physicalEnstrophyRate ν (u t)) (Icc (0 : ℝ) τ) :=
  @MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    -2 * physicalFieldInner (timeDerivative u t) (laplacian (u t)) =
      physicalEnstrophyRate ν (u t) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    HasDerivAt (fun r => physicalDissipation (u r)) (physicalEnstrophyRate ν (u t)) t :=
  @MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC
example : ∃ C : ℝ, 0 < C ∧ ∀ ν T : ℝ, 0 < ν → ∀ a : Field,
      ∀ u : Velocity, ∀ p : Pressure, InitialClassicalFront ν T a u p →
      ∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivAt (fun r => physicalDissipation (u r)) (physicalEnstrophyRate ν (u t)) t ∧
        physicalEnstrophyRate ν (u t) + ν * physicalLaplacianSquare (u t) ≤
          C / ν ^ 3 * physicalDissipation (u t) ^ 3 :=
  @MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (τ : ℝ) (hτT : τ < T),
    ContinuousOn (fun t => physicalDissipation (u t)) (Icc (0 : ℝ) τ) ∧
    ContinuousOn (fun t => Real.sqrt (physicalLaplacianSquare (u t))) (Icc (0 : ℝ) τ) ∧
    ContinuousOn (fun t => physicalEnstrophyRate ν (u t)) (Icc (0 : ℝ) τ) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn"
#check @MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initialFrontSpacetime_uniqueDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin"
#check @MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin"
#print axioms MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_eq_jointWithin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_coordinateDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_laplacian_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn"
#check @MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn"
#print axioms MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_convection_continuousOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc"
#check @MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc"
#print axioms MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc"
#check @MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc"
#print axioms MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_physicalLaplacianSquare_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute"
#check @MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute"
#print axioms MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_time_coordinateDerivative_commute"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic"
#check @MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic"
#print axioms MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_spatialPeriodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt"
#check @MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt"
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free"
#check @MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free"
#print axioms MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_laplacian_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc"
#check @MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc"
#print axioms MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_physicalEnstrophyRate_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing"
#check @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_pairing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt"
#check @MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC"
#check @MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC"
#print axioms MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity"
#check @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_scalar_continuity"
