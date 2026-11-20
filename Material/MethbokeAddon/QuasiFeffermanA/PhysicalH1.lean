import MethbokeAddon.QuasiFeffermanA.Contracts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The physical whole-space H1 gradient graph

Construct the closed graph of the native real compact-test weak gradient in
the actual fourfold L2 Hilbert sum. Its norm is the physical H1 norm. Gradient
uniqueness follows from real compact-test separation, independently of Fourier
theory. The solenoidal restriction is an intersection of actual continuous
test-pairing kernels. Real Schwartz fields supply actual derivative witnesses.

Prepared source: matching authorized external compiler, exact-type and named
axiom evidence are required. No local Lean, Lake or kernel execution is used.
This module asserts no NSE evolution, Fourier realization or regularity root.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology SchwartzMap LineDeriv

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Representation

/-- Compact real tests determine an L2 directional derivative uniquely. -/
theorem realTestWeakDirectionalDerivative_unique
    {v G H : SpatialL2} {e : Space}
    (hG : RealTestWeakDirectionalDerivative v G e)
    (hH : RealTestWeakDirectionalDerivative v H e) : G = H := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp G).locallyIntegrable (by norm_num))
    ((Lp.memLp H).locallyIntegrable (by norm_num))
  intro ψ hψ hcompact
  exact neg_injective ((hG ψ hψ hcompact).symm.trans (hH ψ hψ hcompact))

/-- The native three-component weak-gradient witness is unique. -/
theorem spatialWeakGradient_unique
    {v : SpatialL2} {G H : Fin 3 → SpatialL2}
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakGradient v H) : G = H := by
  funext j
  exact realTestWeakDirectionalDerivative_unique (hG j) (hH j)

/-- The actual continuous test pairing on full-volume spatial L2. -/
def compactPairingCLM (ψ : Space → ℝ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) : SpatialL2 →L[ℝ] Space :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := Space)).lpPairing volume 2 2
    ((hψ.memLp_of_hasCompactSupport hcompact : MemLp ψ 2 volume).toLp ψ)

theorem compactPairingCLM_apply (ψ : Space → ℝ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (v : SpatialL2) :
    compactPairingCLM ψ hψ hcompact v = ∫ x : Space, ψ x • v x := by
  rw [compactPairingCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(hψ.memLp_of_hasCompactSupport hcompact :
    MemLp ψ 2 volume).coeFn_toLp] with x hx
  simp only [ContinuousLinearMap.lsmul_apply, hx]

/-- One real smooth compact spatial test, without PDE hypotheses. -/
structure CompactSmoothScalarTest where
  value : Space → ℝ
  smooth : ContDiff ℝ ∞ value
  compact_support : HasCompactSupport value

/-- Velocity followed by three weak derivatives in their actual Hilbert sum. -/
abbrev H1Ambient := PiLp 2 (fun _ : Fin 4 => SpatialL2)

/-- Insert the actual L2 velocity and weak-gradient fields into the Hilbert sum. -/
def h1Pack (v : SpatialL2) (G : Fin 3 → SpatialL2) : H1Ambient :=
  WithLp.toLp 2 (Fin.cons v G)

@[simp] theorem h1Pack_zero (v : SpatialL2) (G : Fin 3 → SpatialL2) :
    h1Pack v G 0 = v := rfl

@[simp] theorem h1Pack_succ (v : SpatialL2) (G : Fin 3 → SpatialL2) (j : Fin 3) :
    h1Pack v G j.succ = G j := rfl

/-- A physical weak derivative is the zero of this actual continuous pairing. -/
def weakGradientResidual (j : Fin 3) (φ : CompactSmoothScalarTest) :
    H1Ambient →L[ℝ] Space :=
  (compactPairingCLM (fun x => fderiv ℝ φ.value x (coordinateVector j))
      ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (φ.compact_support.fderiv_apply ℝ (coordinateVector j))).comp
      (PiLp.proj 2 (fun _ : Fin 4 => SpatialL2) 0) +
    (compactPairingCLM φ.value φ.smooth.continuous φ.compact_support).comp
      (PiLp.proj 2 (fun _ : Fin 4 => SpatialL2) j.succ)

theorem weakGradientResidual_apply (j : Fin 3) (φ : CompactSmoothScalarTest)
    (x : H1Ambient) :
    weakGradientResidual j φ x =
      (∫ y : Space, fderiv ℝ φ.value y (coordinateVector j) • x 0 y) +
      ∫ y : Space, φ.value y • x j.succ y := by
  simp only [weakGradientResidual, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, compactPairingCLM_apply]

/-- Closed physical weak-gradient graph, constructed from continuous kernels. -/
def physicalH1Graph : ClosedSubmodule ℝ H1Ambient :=
  ⨅ j : Fin 3, ⨅ φ : CompactSmoothScalarTest,
    (⟨(weakGradientResidual j φ).ker,
      (weakGradientResidual j φ).isClosed_ker⟩ : ClosedSubmodule ℝ H1Ambient)

theorem mem_physicalH1Graph_iff (x : H1Ambient) :
    x ∈ physicalH1Graph ↔ SpatialWeakGradient (x 0) (fun j => x j.succ) := by
  simp only [physicalH1Graph, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_mk,
    LinearMap.mem_ker]
  constructor
  · intro h j ψ hψ hcompact
    have hzero := h j ⟨ψ, hψ, hcompact⟩
    rw [weakGradientResidual_apply] at hzero
    exact eq_neg_iff_add_eq_zero.mpr hzero
  · intro h j φ
    rw [weakGradientResidual_apply]
    exact eq_neg_iff_add_eq_zero.mp (h j φ.value φ.smooth φ.compact_support)

/-- The physical H1 carrier, with its inherited sum-of-squares Hilbert norm. -/
abbrev PhysicalH1 := physicalH1Graph.toSubmodule

instance physicalH1CompleteSpace : CompleteSpace PhysicalH1 :=
  physicalH1Graph.isClosed.isComplete.completeSpace_coe

theorem physicalH1_isClosed : IsClosed (physicalH1Graph : Set H1Ambient) :=
  physicalH1Graph.isClosed

/-- The actual velocity map on the physical H1 graph. -/
def physicalH1Velocity : PhysicalH1 →L[ℝ] SpatialL2 :=
  (PiLp.proj 2 (fun _ : Fin 4 => SpatialL2) 0).comp physicalH1Graph.toSubmodule.subtypeL

/-- Each actual weak derivative is a bounded linear map out of physical H1. -/
def physicalH1Gradient (j : Fin 3) : PhysicalH1 →L[ℝ] SpatialL2 :=
  (PiLp.proj 2 (fun _ : Fin 4 => SpatialL2) j.succ).comp
    physicalH1Graph.toSubmodule.subtypeL

theorem physicalH1_weakGradient (u : PhysicalH1) :
    SpatialWeakGradient (physicalH1Velocity u) (fun j => physicalH1Gradient j u) :=
  (mem_physicalH1Graph_iff u.val).mp u.property

theorem physicalH1_norm_sq (u : PhysicalH1) :
    ‖u‖ ^ 2 = ‖physicalH1Velocity u‖ ^ 2 +
      ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 := by
  change ‖u.val‖ ^ 2 = ‖u.val 0‖ ^ 2 + ∑ j : Fin 3, ‖u.val j.succ‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]

theorem physicalH1Velocity_injective : Function.Injective physicalH1Velocity := by
  intro u v huv
  have hgrad : (fun j => physicalH1Gradient j u) =
      (fun j => physicalH1Gradient j v) := by
    apply spatialWeakGradient_unique (physicalH1_weakGradient u)
    rw [huv]
    exact physicalH1_weakGradient v
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact huv
  · exact congrFun hgrad j

/-- A concrete native weak-gradient witness constructs a physical H1 element. -/
def physicalH1OfWeakGradient (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : SpatialWeakGradient v G) : PhysicalH1 :=
  ⟨h1Pack v G, (mem_physicalH1Graph_iff _).mpr h⟩

@[simp] theorem physicalH1OfWeakGradient_velocity (v : SpatialL2)
    (G : Fin 3 → SpatialL2) (h : SpatialWeakGradient v G) :
    physicalH1Velocity (physicalH1OfWeakGradient v G h) = v := rfl

@[simp] theorem physicalH1OfWeakGradient_gradient (v : SpatialL2)
    (G : Fin 3 → SpatialL2) (h : SpatialWeakGradient v G) (j : Fin 3) :
    physicalH1Gradient j (physicalH1OfWeakGradient v G h) = G j := rfl

theorem scalarGradient_continuous {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (scalarGradient ψ) := by
  unfold scalarGradient
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun j =>
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem scalarGradient_hasCompactSupport {ψ : Space → ℝ}
    (hcompact : HasCompactSupport ψ) : HasCompactSupport (scalarGradient ψ) := by
  exact (hcompact.fderiv ℝ).comp_left
    (g := fun L : Space →L[ℝ] ℝ =>
      WithLp.toLp 2 (fun j : Fin 3 => L (coordinateVector j))) (by rfl)

/-- The actual L2 gradient of a compact smooth scalar test. -/
def scalarTestGradientL2 (φ : CompactSmoothScalarTest) : SpatialL2 :=
  ((scalarGradient_continuous φ.smooth).memLp_of_hasCompactSupport
    (scalarGradient_hasCompactSupport φ.compact_support) :
      MemLp (scalarGradient φ.value) 2 volume).toLp (scalarGradient φ.value)

theorem scalarTestGradientL2_ae (φ : CompactSmoothScalarTest) :
    scalarTestGradientL2 φ =ᵐ[volume] scalarGradient φ.value :=
  MemLp.coeFn_toLp _

/-- Divergence testing is an actual continuous L2 inner-product functional. -/
def solenoidalTestCLM (φ : CompactSmoothScalarTest) : SpatialL2 →L[ℝ] ℝ :=
  innerSL ℝ (scalarTestGradientL2 φ)

theorem solenoidalTestCLM_apply (φ : CompactSmoothScalarTest) (v : SpatialL2) :
    solenoidalTestCLM φ v =
      ∫ x : Space, inner ℝ (v x) (scalarGradient φ.value x) := by
  rw [solenoidalTestCLM, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarTestGradientL2_ae φ] with x hx
  rw [hx, real_inner_comm]

theorem integrable_solenoidalTest (φ : CompactSmoothScalarTest) (v : SpatialL2) :
    Integrable (fun x : Space => inner ℝ (v x) (scalarGradient φ.value x)) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) v (scalarTestGradientL2 φ)).congr
  filter_upwards [scalarTestGradientL2_ae φ] with x hx
  rw [hx]

theorem solenoidal_iff_testCLM (v : SpatialL2) :
    Solenoidal v ↔ ∀ φ : CompactSmoothScalarTest, solenoidalTestCLM φ v = 0 := by
  constructor
  · intro h φ
    rw [solenoidalTestCLM_apply]
    exact (h φ.value φ.smooth φ.compact_support).2
  · intro h ψ hψ hcompact
    let φ : CompactSmoothScalarTest := ⟨ψ, hψ, hcompact⟩
    exact ⟨integrable_solenoidalTest φ v,
      (solenoidalTestCLM_apply φ v).symm.trans (h φ)⟩

/-- Closed solenoidal restriction of the actual physical gradient graph. -/
def physicalH1SigmaGraph : ClosedSubmodule ℝ H1Ambient :=
  physicalH1Graph ⊓
    ⨅ φ : CompactSmoothScalarTest,
      let L := (solenoidalTestCLM φ).comp (PiLp.proj 2 (fun _ : Fin 4 => SpatialL2) 0)
      (⟨L.ker, L.isClosed_ker⟩ : ClosedSubmodule ℝ H1Ambient)

theorem mem_physicalH1SigmaGraph_iff (x : H1Ambient) :
    x ∈ physicalH1SigmaGraph ↔
      SpatialWeakGradient (x 0) (fun j => x j.succ) ∧ Solenoidal (x 0) := by
  simp only [physicalH1SigmaGraph, ClosedSubmodule.mem_inf, mem_physicalH1Graph_iff,
    ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_mk, LinearMap.mem_ker,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, solenoidal_iff_testCLM]

/-- Complete real solenoidal H1 on full Euclidean space. -/
abbrev PhysicalH1Sigma := physicalH1SigmaGraph.toSubmodule

instance physicalH1SigmaCompleteSpace : CompleteSpace PhysicalH1Sigma :=
  physicalH1SigmaGraph.isClosed.isComplete.completeSpace_coe

theorem physicalH1Sigma_isClosed : IsClosed (physicalH1SigmaGraph : Set H1Ambient) :=
  physicalH1SigmaGraph.isClosed

theorem physicalH1Sigma_weakGradient (u : PhysicalH1Sigma) :
    SpatialWeakGradient (u.val 0) (fun j => u.val j.succ) :=
  ((mem_physicalH1SigmaGraph_iff u.val).mp u.property).1

theorem physicalH1Sigma_solenoidal (u : PhysicalH1Sigma) : Solenoidal (u.val 0) :=
  ((mem_physicalH1SigmaGraph_iff u.val).mp u.property).2

theorem physicalH1Sigma_norm_sq (u : PhysicalH1Sigma) :
    ‖u‖ ^ 2 = ‖u.val 0‖ ^ 2 + ∑ j : Fin 3, ‖u.val j.succ‖ ^ 2 := by
  change ‖u.val‖ ^ 2 = ‖u.val 0‖ ^ 2 + ∑ j : Fin 3, ‖u.val j.succ‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]

theorem physicalH1Sigma_velocity_injective :
    Function.Injective (fun u : PhysicalH1Sigma => u.val 0) := by
  intro u v huv
  have hgrad : (fun j : Fin 3 => u.val j.succ) = (fun j : Fin 3 => v.val j.succ) := by
    apply spatialWeakGradient_unique (physicalH1Sigma_weakGradient u)
    rw [huv]
    exact physicalH1Sigma_weakGradient v
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact huv
  · exact congrFun hgrad j

/-- Real Schwartz fields have their actual classical derivatives as weak witnesses. -/
theorem schwartz_spatialWeakGradient (a : 𝓢(Space, Space)) :
    SpatialWeakGradient (a.toLp 2 volume)
      (fun j => (∂_{coordinateVector j} a).toLp 2 volume) := by
  intro j ψ hψ hcompact
  let φ : 𝓢(Space, ℝ) := hcompact.toSchwartzMap hψ
  have hparts := SchwartzMap.integral_smul_lineDerivOp_right_eq_neg_left
    (μ := (volume : Measure Space)) φ a (coordinateVector j)
  calc
    (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • a.toLp 2 volume x) =
        ∫ x : Space, (∂_{coordinateVector j} φ) x • a x := by
      apply integral_congr_ae
      filter_upwards [a.coeFn_toLp 2 volume] with x hx
      rw [hx]
      rfl
    _ = -(∫ x : Space, φ x • (∂_{coordinateVector j} a) x) := by
      simpa only [neg_neg] using congrArg Neg.neg hparts.symm
    _ = -(∫ x : Space, ψ x • (∂_{coordinateVector j} a).toLp 2 volume x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(∂_{coordinateVector j} a).coeFn_toLp 2 volume] with x hx
      rw [hx]
      rfl

/-- Actual Schwartz data admission into the physical H1 graph. -/
def schwartzToPhysicalH1 (a : 𝓢(Space, Space)) : PhysicalH1 :=
  physicalH1OfWeakGradient (a.toLp 2 volume)
    (fun j => (∂_{coordinateVector j} a).toLp 2 volume) (schwartz_spatialWeakGradient a)

@[simp] theorem schwartzToPhysicalH1_velocity (a : 𝓢(Space, Space)) :
    physicalH1Velocity (schwartzToPhysicalH1 a) = a.toLp 2 volume := rfl

/-- Native real solenoidal Schwartz data admit into the complete H1_sigma carrier. -/
def schwartzToPhysicalH1Sigma (a : 𝓢(Space, Space))
    (hsol : Solenoidal (a.toLp 2 volume)) : PhysicalH1Sigma :=
  ⟨h1Pack (a.toLp 2 volume) (fun j => (∂_{coordinateVector j} a).toLp 2 volume),
    (mem_physicalH1SigmaGraph_iff _).mpr ⟨schwartz_spatialWeakGradient a, hsol⟩⟩

@[simp] theorem schwartzToPhysicalH1Sigma_velocity (a : 𝓢(Space, Space))
    (hsol : Solenoidal (a.toLp 2 volume)) :
    (schwartzToPhysicalH1Sigma a hsol).val 0 = a.toLp 2 volume := rfl

end MethbokeAddon.QuasiFeffermanA
