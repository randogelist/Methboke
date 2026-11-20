import QFAPhysicalH1Sectors.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ENNReal ContDiff

namespace QFAPhysicalH1Sectors.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
open MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Literal full-volume real and complex vector carriers.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : H1Ambient = PiLp 2 (fun _ : Fin 4 =>
    Lp (EuclideanSpace ℝ (Fin 3)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := rfl
example : PhysicalH1 = physicalH1Graph.toSubmodule := rfl

-- The native graph retains every actual compact smooth real test and sign.
example (x : H1Ambient) : x ∈ physicalH1Graph ↔
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y : Space, fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ)) • x 0 y) =
        -(∫ y : Space, ψ y • x j.succ y) := mem_physicalH1Graph_iff x
example (u : PhysicalH1) : physicalH1Velocity u = u.val 0 := rfl
example (u : PhysicalH1) (j : Fin 3) : physicalH1Gradient j u = u.val j.succ := rfl

-- H01: the projected derivative conclusion is not among the assumptions.
example (i : Fin 6) (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
        -(∫ x : Space, ψ x • G j x)) :
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) •
        realFourierSector i v x) =
          -(∫ x : Space, ψ x • realFourierSector i (G j) x) :=
  spatialWeakGradient_realFourierSector i h

-- H02: actual projected velocity and projected supplied gradients form the graph.
example (i : Fin 6) (u : PhysicalH1) : PhysicalH1 := physicalH1Sector i u
example (i : Fin 6) (u : PhysicalH1) :
    (physicalH1Sector i u).val = WithLp.toLp 2
      (Fin.cons (realFourierSector i (physicalH1Velocity u))
        (fun j => realFourierSector i (physicalH1Gradient j u))) := rfl
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1Sector i u = physicalH1OfWeakGradient
      (realFourierSector i (physicalH1Velocity u))
      (fun j => realFourierSector i (physicalH1Gradient j u))
      (spatialWeakGradient_realFourierSector i (physicalH1_weakGradient u)) := rfl

example (i : Fin 6) (u : PhysicalH1) :
    physicalH1Velocity (physicalH1Sector i u) = realFourierSector i (physicalH1Velocity u) :=
  physicalH1Sector_velocity i u
example (i : Fin 6) (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (physicalH1Sector i u) =
      realFourierSector i (physicalH1Gradient j u) := physicalH1Sector_gradient i u j
example (i : Fin 6) (u v : PhysicalH1) :
    physicalH1Sector i (u + v) = physicalH1Sector i u + physicalH1Sector i v :=
  physicalH1Sector_add i u v
example (i : Fin 6) (r : ℝ) (u : PhysicalH1) :
    physicalH1Sector i (r • u) = r • physicalH1Sector i u := physicalH1Sector_smul i r u
example (i : Fin 6) : physicalH1Sector i 0 = 0 := physicalH1Sector_zero i
example (i : Fin 6) (u : PhysicalH1) : ‖physicalH1Sector i u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
  physicalH1Sector_norm_sq_le i u
example (i : Fin 6) (u : PhysicalH1) : ‖physicalH1Sector i u‖ ≤ ‖u‖ :=
  norm_physicalH1Sector_le i u
example (i : Fin 6) : PhysicalH1 →L[ℝ] PhysicalH1 := physicalH1SectorCLM i
example (i : Fin 6) (u : PhysicalH1) : physicalH1SectorCLM i u = physicalH1Sector i u :=
  physicalH1SectorCLM_apply i u
example (i : Fin 6) (u : PhysicalH1) :
    (physicalH1SectorCLM i u).val = WithLp.toLp 2
      (Fin.cons (realFourierSector i (physicalH1Velocity u))
        (fun j => realFourierSector i (physicalH1Gradient j u))) := rfl
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1Sector i (physicalH1Sector i u) = physicalH1Sector i u :=
  physicalH1Sector_idempotent i u
example (i k : Fin 6) (hik : i ≠ k) (u : PhysicalH1) :
    physicalH1Sector i (physicalH1Sector k u) = 0 := physicalH1Sector_comp_eq_zero hik u
example (u : PhysicalH1) : (∑ i : Fin 6, physicalH1Sector i u) = u :=
  sum_physicalH1Sector u

-- The inhomogeneous H1 inner product includes the velocity term.
example (u v : PhysicalH1) :
    inner ℝ u v = inner ℝ (physicalH1Velocity u) (physicalH1Velocity v) +
      ∑ j : Fin 3, inner ℝ (physicalH1Gradient j u) (physicalH1Gradient j v) :=
  physicalH1_inner_eq u v
example (i : Fin 6) (u v : PhysicalH1) :
    inner ℝ (physicalH1Sector i u) v = inner ℝ u (physicalH1Sector i v) :=
  inner_physicalH1Sector_left i u v
example (i k : Fin 6) (hik : i ≠ k) (u v : PhysicalH1) :
    inner ℝ (physicalH1Sector i u) (physicalH1Sector k v) = 0 :=
  inner_physicalH1Sector_eq_zero hik u v
example (u : PhysicalH1) : (∑ i : Fin 6, ‖physicalH1Sector i u‖ ^ 2) = ‖u‖ ^ 2 :=
  sum_norm_physicalH1Sector_sq u

-- Literal physical gradient charges and the independent exact finite sum.
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1Enstrophy (physicalH1Sector i u) =
      ∑ j : Fin 3, ‖realFourierSector i (physicalH1Gradient j u)‖ ^ 2 :=
  physicalH1Enstrophy_sector i u
example (u : PhysicalH1) :
    (∑ i : Fin 6, physicalH1Enstrophy (physicalH1Sector i u)) = physicalH1Enstrophy u :=
  sum_physicalH1Enstrophy_sector u
example (i : Fin 6) (u : PhysicalH1) : ℝ := physicalH1SectorCharge i u
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u = ∑ j : Fin 3, ‖(physicalH1Sector i u).val j.succ‖ ^ 2 := rfl
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u =
      ∑ j : Fin 3, ‖realFourierSector i (physicalH1Gradient j u)‖ ^ 2 :=
  physicalH1SectorCharge_eq i u
example (i : Fin 6) (u : PhysicalH1) : 0 ≤ physicalH1SectorCharge i u :=
  physicalH1SectorCharge_nonneg i u
example (u : PhysicalH1) :
    (∑ i : Fin 6, physicalH1SectorCharge i u) = physicalH1Enstrophy u :=
  sum_physicalH1SectorCharge u
example (i : Fin 6) : Continuous (physicalH1SectorCharge i) :=
  physicalH1SectorCharge_continuous i
example (i : Fin 6) (U : ℝ → PhysicalH1) (s : Set ℝ) (hU : ContinuousOn U s) :
    ContinuousOn (fun t => physicalH1SectorCharge i (U t)) s :=
  physicalH1SectorCharge_continuousOn i U hU

-- Actual weighted integrability precedes the exact 4*pi^2 identities.
example (i : Fin 6) (u : PhysicalH1) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity (physicalH1Sector i u))) : ComplexL2) ξ‖ ^ 2)
      volume := physicalH1Sector_fourier_weighted_integrable i u
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u = (4 * Real.pi ^ 2) *
      (∫ ξ : Space, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity (physicalH1Sector i u))) : ComplexL2) ξ‖ ^ 2) :=
  physicalH1SectorCharge_eq_fourier i u
example (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u = (4 * Real.pi ^ 2) *
      (∫ ξ : Space in sixSector i, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  physicalH1SectorCharge_eq_sector_integral i u

-- The original pointwise factor-six endpoint uses the constructed physical charges.
example (u : PhysicalH1) :
    (∑ i : Fin 6, (physicalH1SectorCharge i u) ^ 2) ≤ (physicalH1Enstrophy u) ^ 2 ∧
      (physicalH1Enstrophy u) ^ 2 ≤ 6 * ∑ i : Fin 6, (physicalH1SectorCharge i u) ^ 2 :=
  physicalH1Sector_charge_sq_bounds u

-- Full stopped windows and extended values are preserved literally.
example (U : ℝ → PhysicalH1) (b : ℝ) :
    sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
      (volume.restrict (Ioo (0 : ℝ) b)) =
        ∫⁻ t in Ioo (0 : ℝ) b,
          ENNReal.ofReal (∑ i : Fin 6,
            (∑ j : Fin 3, ‖realFourierSector i (physicalH1Gradient j (U t))‖ ^ 2) ^ 2) := rfl
example (U : ℝ → PhysicalH1) (b : ℝ) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b =
      ∫⁻ t in Ioo (0 : ℝ) b,
        ENNReal.ofReal ((∑ j : Fin 3, ‖physicalH1Gradient j (U t)‖ ^ 2) ^ 2) := rfl

example (U : ℝ → PhysicalH1) (b : ℝ) :
    sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) ≤
      stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ∧
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≤
      6 * sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) := physicalH1Sector_budget_bounds U b
example (U : ℝ → PhysicalH1) (b : ℝ) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≠ ∞ ↔
      sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) ≠ ∞ := physicalH1Sector_budget_finite_iff U b
example (U : ℝ → PhysicalH1) (b : ℝ) (hU : ContinuousOn U (Ioo (0 : ℝ) b)) :
    sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) =
      ∑ i : Fin 6, ∫⁻ t in Ioo (0 : ℝ) b,
        ENNReal.ofReal ((physicalH1SectorCharge i (U t)) ^ 2) :=
  physicalH1Sector_budget_eq_sum U b hU
example (U : ℝ → PhysicalH1) (b : ℝ) (hU : ContinuousOn U (Ioo (0 : ℝ) b)) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≠ ∞ ↔
      ∀ i : Fin 6, (∫⁻ t in Ioo (0 : ℝ) b,
        ENNReal.ofReal ((physicalH1SectorCharge i (U t)) ^ 2)) ≠ ∞ :=
  physicalH1Sector_budget_finite_iff_each U b hU

end QFAPhysicalH1Sectors.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_add"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_add"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_smul"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_zero"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_norm_sq_le"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH1Sector_le"
#check @MethbokeAddon.QuasiFeffermanA.norm_physicalH1Sector_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH1Sector_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH1Sector_le"
#print axioms MethbokeAddon.QuasiFeffermanA.norm_physicalH1Sector_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH1Sector_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_comp_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_comp_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_comp_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_comp_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_comp_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_comp_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Sector"
#check @MethbokeAddon.QuasiFeffermanA.sum_physicalH1Sector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Sector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Sector"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_physicalH1Sector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Sector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_inner_eq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_inner_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_inner_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_inner_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_inner_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_inner_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_left"
#check @MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_left"
#print axioms MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1Sector_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1Sector_sq"
#check @MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1Sector_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1Sector_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1Sector_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1Sector_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1Sector_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_sector"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_sector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_sector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_sector"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_sector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_sector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Enstrophy_sector"
#check @MethbokeAddon.QuasiFeffermanA.sum_physicalH1Enstrophy_sector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Enstrophy_sector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Enstrophy_sector"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_physicalH1Enstrophy_sector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1Enstrophy_sector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SectorCharge"
#check @MethbokeAddon.QuasiFeffermanA.sum_physicalH1SectorCharge
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SectorCharge"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SectorCharge"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_physicalH1SectorCharge
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SectorCharge"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuous"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuousOn"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuousOn
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuousOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuousOn"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuousOn
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_continuousOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_fourier_weighted_integrable"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_fourier_weighted_integrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_fourier_weighted_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_fourier_weighted_integrable"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_fourier_weighted_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_fourier_weighted_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_sector_integral"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_sector_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_sector_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_sector_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_sector_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SectorCharge_eq_sector_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_charge_sq_bounds"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_charge_sq_bounds
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_charge_sq_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_charge_sq_bounds"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_charge_sq_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_charge_sq_bounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_bounds"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_bounds
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_bounds"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_bounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_eq_sum"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_eq_sum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_eq_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_eq_sum"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_eq_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_eq_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff_each"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff_each
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff_each"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff_each"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff_each
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sector_budget_finite_iff_each"
