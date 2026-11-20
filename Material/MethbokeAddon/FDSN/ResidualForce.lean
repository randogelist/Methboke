import MethbokeAddon.EhrenfestObstruction.CrossTransport
import MethbokeAddon.FeffermanFamily.LocalDifferential

/-!
# Exact residual forcing for the native torus NSE operators

All derivatives are the concrete operators of SingularClosure.Contracts.
The native time derivative retains its derivWithin (Ici 0) convention.
The theorem is algebraic in viscosity and requires no seed-existence assertion.
-/

set_option autoImplicit false

noncomputable section

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

/-- The actual residual force realizing the velocity perturbation U+h while
retaining the pressure. The mixed terms are the literal bilinear transport. -/
def residualForce (ν : ℝ) (U F h : Velocity) : Velocity :=
  fun t x =>
    F t x + timeDerivative h t x - ν • laplacian (h t) x +
      physicalTransport (U t) (h t) x +
      physicalTransport (h t) (U t) x + convection (h t) x

theorem native_coordinateDerivative_contDiff
    (a : Field) (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative a i) := by
  exact (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem native_coordinateDerivative_add
    (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (i : Fin 3) :
    coordinateDerivative (a + b) i =
      coordinateDerivative a i + coordinateDerivative b i := by
  funext x
  change fderiv ℝ (a + b) x (unitVector i) =
    fderiv ℝ a x (unitVector i) + fderiv ℝ b x (unitVector i)
  rw [fderiv_add (ha.differentiable (by norm_num) x)
    (hb.differentiable (by norm_num) x), ContinuousLinearMap.add_apply]

theorem native_laplacian_add
    (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    laplacian (a + b) = laplacian a + laplacian b := by
  funext x
  change laplacian (a + b) x = laplacian a x + laplacian b x
  unfold laplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [native_coordinateDerivative_add a b ha hb i]
  rw [fderiv_add
    ((native_coordinateDerivative_contDiff a ha i).differentiable (by norm_num) x)
    ((native_coordinateDerivative_contDiff b hb i).differentiable (by norm_num) x),
    ContinuousLinearMap.add_apply]

theorem native_divergence_add
    (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (x : Vec) :
    divergence (a + b) x = divergence a x + divergence b x := by
  unfold divergence
  simp_rw [native_coordinateDerivative_add a b ha hb]
  simp only [Pi.add_apply, Finset.sum_add_distrib]

theorem native_timeDerivative_add
    (U h : Velocity) (t : ℝ) (x : Vec)
    (hU : DifferentiableWithinAt ℝ (fun r => U r x) (Ici (0 : ℝ)) t)
    (hh : DifferentiableWithinAt ℝ (fun r => h r x) (Ici (0 : ℝ)) t) :
    timeDerivative (U + h) t x = timeDerivative U t x + timeDerivative h t x := by
  simpa only [timeDerivative, Pi.add_apply] using derivWithin_add hU hh

/-- Exact momentum-equation realization at a point, with actual spatial
smoothness and actual one-sided time differentiability as hypotheses. -/
theorem native_residual_momentum_at
    (ν : ℝ) (U F h : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hU : ContDiff ℝ ∞ (U t)) (hh : ContDiff ℝ ∞ (h t))
    (hUt : DifferentiableWithinAt ℝ (fun r => U r x) (Ici (0 : ℝ)) t)
    (hht : DifferentiableWithinAt ℝ (fun r => h r x) (Ici (0 : ℝ)) t)
    (hNSE : timeDerivative U t x + convection (U t) x +
        SingularClosure.gradient (p t) x =
      ν • laplacian (U t) x + F t x) :
    timeDerivative (U + h) t x + convection ((U + h) t) x +
        SingularClosure.gradient (p t) x =
      ν • laplacian ((U + h) t) x + residualForce ν U F h t x := by
  have hdt := native_timeDerivative_add U h t x hUt hht
  have hconv := congrFun (convection_add_eq_transport (U t) (h t) hU hh) x
  have hlap := congrFun (native_laplacian_add (U t) (h t) hU hh) x
  simp only [Pi.add_apply] at hconv hlap
  change timeDerivative (U + h) t x + convection (U t + h t) x +
      SingularClosure.gradient (p t) x =
    ν • laplacian (U t + h t) x + residualForce ν U F h t x
  rw [hdt, hconv, hlap]
  unfold residualForce
  calc
    _ = (timeDerivative U t x + convection (U t) x +
        SingularClosure.gradient (p t) x) +
      (timeDerivative h t x + physicalTransport (U t) (h t) x +
        physicalTransport (h t) (U t) x + convection (h t) x) := by abel
    _ = (ν • laplacian (U t) x + F t x) +
      (timeDerivative h t x + physicalTransport (U t) (h t) x +
        physicalTransport (h t) (U t) x + convection (h t) x) := by rw [hNSE]
    _ = _ := by rw [smul_add]; abel

/-- A smooth divergence-free correction preserves incompressibility. -/
theorem native_divergence_add_zero
    (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hda : ∀ x : Vec, divergence a x = 0)
    (hdb : ∀ x : Vec, divergence b x = 0) :
    ∀ x : Vec, divergence (a + b) x = 0 := by
  intro x
  rw [native_divergence_add a b ha hb x, hda x, hdb x, add_zero]

/-- The pointwise realization applies throughout an open regular time slab.
The time differentiability assumptions are derived from joint smoothness. -/
theorem native_residual_momentum_on_open_slab
    (ν : ℝ) (U F h : Velocity) (p : Pressure) (s T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2)
      {z | z.1 ∈ Ioo s T})
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2)
      {z | z.1 ∈ Ioo s T})
    (hNSE : ∀ t ∈ Ioo s T, ∀ x : Vec,
      timeDerivative U t x + convection (U t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (U t) x + F t x) :
    ∀ t ∈ Ioo s T, ∀ x : Vec,
      timeDerivative (U + h) t x + convection ((U + h) t) x +
          SingularClosure.gradient (p t) x =
        ν • laplacian ((U + h) t) x + residualForce ν U F h t x := by
  intro t ht x
  have hopen : IsOpen {z : ℝ × Vec | z.1 ∈ Ioo s T} :=
    isOpen_Ioo.preimage continuous_fst
  have hUsp : ContDiff ℝ ∞ (U t) := by
    rw [← contDiffOn_univ]
    exact hU.comp (g := fun y : Vec => (t, y))
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ht)
  have hhsp : ContDiff ℝ ∞ (h t) := by
    rw [← contDiffOn_univ]
    exact hh.comp (g := fun y : Vec => (t, y))
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ht)
  have hUat : ContDiffAt ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (t, x) :=
    hU.contDiffAt (hopen.mem_nhds ht)
  have hhat : ContDiffAt ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (t, x) :=
    hh.contDiffAt (hopen.mem_nhds ht)
  have hUt : ContDiffAt ℝ ∞ (fun r : ℝ => U r x) t :=
    hUat.comp t (contDiffAt_id.prodMk (contDiffAt_const (c := x)))
  have hht : ContDiffAt ℝ ∞ (fun r : ℝ => h r x) t :=
    hhat.comp t (contDiffAt_id.prodMk (contDiffAt_const (c := x)))
  exact native_residual_momentum_at ν U F h p t x hUsp hhsp
    (hUt.differentiableAt (by norm_num)).differentiableWithinAt
    (hht.differentiableAt (by norm_num)).differentiableWithinAt (hNSE t ht x)

end MethbokeAddon.FDSN

