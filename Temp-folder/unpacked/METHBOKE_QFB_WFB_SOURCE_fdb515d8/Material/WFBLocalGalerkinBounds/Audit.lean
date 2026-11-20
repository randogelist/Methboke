import WFBLocalGalerkinBounds.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos
example : 0 < galerkinEnstrophyConstant :=
  @MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (N : ℕ)
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t),
    ∃ d : ℝ,
      HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r)) d (Ici 0) t ∧
        d + ν * coefficientLaplacianSquare N (g.coeff t) ≤
          galerkinEnstrophyConstant / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 :=
  @MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos
example : ∀ {ν R : ℝ} (hν : 0 < ν) (hR : 0 ≤ R),
    0 < localGalerkinTime ν R :=
  @MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg
example : ∀ {ν R : ℝ} (hR : 0 ≤ R),
    0 ≤ localGalerkinAccumulationBound ν R :=
  @MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (N : ℕ)
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t),
    coefficientEnstrophyRate ν N (g.coeff t) +
        ν * coefficientLaplacianSquare N (g.coeff t) ≤
      galerkinEnstrophyConstant / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 :=
  @MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation
example : ∀ (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R),
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      ∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        coefficientDissipation N (g.coeff t) ≤ 2 * (R + 1) ∧
        coefficientDissipation N (g.coeff t) +
            ν * (∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s)) ≤
          localGalerkinAccumulationBound ν R :=
  @MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation
example : ∀ (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R),
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      ∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        physicalDissipation (g.velocity t) ≤ 2 * (R + 1) ∧
        physicalDissipation (g.velocity t) +
            ν * (∫ s in (0 : ℝ)..t,
              ∫ x in unitCube, ‖laplacian (g.velocity s) x‖ ^ 2) ≤
          localGalerkinAccumulationBound ν R :=
  @MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds
example : ∀ (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R),
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      (∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        ‖g.sobolevState 1 t‖ ^ 2 ≤ 4 * (R + 1)) ∧
      IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2)
        volume 0 (localGalerkinTime ν R) ∧
      (∫ t in (0 : ℝ)..(localGalerkinTime ν R), ‖g.sobolevState 2 t‖ ^ 2) ≤
        6 * (R + 1) * localGalerkinTime ν R + localGalerkinAccumulationBound ν R / ν :=
  @MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos"
#check @MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos"
#print axioms MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound"
#check @MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound"
#print axioms MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.galerkinEnstrophyConstant_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos"
#check @MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos"
#print axioms MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.localGalerkinTime_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg"
#check @MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg"
#print axioms MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.localGalerkinAccumulationBound_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality"
#check @MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality"
#print axioms MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.galerkin_local_cubic_inequality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation"
#check @MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation"
#print axioms MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_enstrophy_accumulation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation"
#check @MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation"
#print axioms MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_physical_accumulation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds"
#check @MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds"
#print axioms MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds"
