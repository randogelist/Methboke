import MethbokeAddon.QuasiFeffermanA.PhysicalH1
import MethbokeAddon.QuasiFeffermanA.H1Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The actual thirteen-component physical H2 graph

Velocity, three first derivatives and nine second derivatives live in the
full-volume real L2 Hilbert sum. Every derivative is defined by the existing
compact smooth real tests. The graph is closed, complete, and injects into the
accepted physical H1 graph. Its diagonal Hessian sum is the actual L2
distributional Laplacian. No Fourier norm identity or higher derivative
membership is assumed.

Prepared source requires matching authorized external compiler and independent
exact-type/axiom evidence. No local Lean, Lake, kernel or runner is executed.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology SchwartzMap LineDeriv Laplacian

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Representation
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector SchwartzDerivativeWitnesses)

/-- The four H1 entries and nine ordered Hessian entries remain distinct. -/
abbrev H2Index := Fin 4 ⊕ (Fin 3 × Fin 3)

theorem card_H2Index : Fintype.card H2Index = 13 := by
  simp [H2Index]

/-- The actual thirteenfold real-vector L2 Hilbert sum. -/
abbrev H2Ambient := PiLp 2 (fun _ : H2Index => SpatialL2)

def h2Pack (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2) : H2Ambient :=
  WithLp.toLp 2 (Sum.elim (Fin.cons v G) (fun p => H p.1 p.2))

@[simp] theorem h2Pack_velocity (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2) : h2Pack v G H (Sum.inl 0) = v := rfl

@[simp] theorem h2Pack_gradient (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2) (j : Fin 3) :
    h2Pack v G H (Sum.inl j.succ) = G j := rfl

@[simp] theorem h2Pack_hessian (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2) (j k : Fin 3) :
    h2Pack v G H (Sum.inr (j, k)) = H j k := rfl

/-- The k-th weak derivative of the j-th supplied gradient is H j k. -/
def SpatialWeakHessian (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2) : Prop :=
  ∀ j : Fin 3, SpatialWeakGradient (G j) (H j)

theorem spatialWeakHessian_unique {G : Fin 3 → SpatialL2}
    {H K : Fin 3 → Fin 3 → SpatialL2}
    (hH : SpatialWeakHessian G H) (hK : SpatialWeakHessian G K) : H = K := by
  funext j
  exact spatialWeakGradient_unique (hH j) (hK j)

/-- The native derivative relation is an actual continuous pairing kernel. -/
def weakH2Residual (a b : H2Index) (k : Fin 3)
    (φ : CompactSmoothScalarTest) : H2Ambient →L[ℝ] Space :=
  (compactPairingCLM (fun x => fderiv ℝ φ.value x (coordinateVector k))
      ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (φ.compact_support.fderiv_apply ℝ (coordinateVector k))).comp
      (PiLp.proj 2 (fun _ : H2Index => SpatialL2) a) +
    (compactPairingCLM φ.value φ.smooth.continuous φ.compact_support).comp
      (PiLp.proj 2 (fun _ : H2Index => SpatialL2) b)

theorem weakH2Residual_apply (a b : H2Index) (k : Fin 3)
    (φ : CompactSmoothScalarTest) (x : H2Ambient) :
    weakH2Residual a b k φ x =
      (∫ y : Space, fderiv ℝ φ.value y (coordinateVector k) • x a y) +
        ∫ y : Space, φ.value y • x b y := by
  simp only [weakH2Residual, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, compactPairingCLM_apply]

/-- The closed graph enforces both the first and the second weak derivatives. -/
def physicalH2Graph : ClosedSubmodule ℝ H2Ambient :=
  (⨅ j : Fin 3, ⨅ φ : CompactSmoothScalarTest,
    (⟨(weakH2Residual (Sum.inl 0) (Sum.inl j.succ) j φ).ker,
      (weakH2Residual (Sum.inl 0) (Sum.inl j.succ) j φ).isClosed_ker⟩ :
        ClosedSubmodule ℝ H2Ambient)) ⊓
  (⨅ j : Fin 3, ⨅ k : Fin 3, ⨅ φ : CompactSmoothScalarTest,
    (⟨(weakH2Residual (Sum.inl j.succ) (Sum.inr (j, k)) k φ).ker,
      (weakH2Residual (Sum.inl j.succ) (Sum.inr (j, k)) k φ).isClosed_ker⟩ :
        ClosedSubmodule ℝ H2Ambient))

theorem mem_physicalH2Graph_iff (x : H2Ambient) :
    x ∈ physicalH2Graph ↔
      SpatialWeakGradient (x (Sum.inl 0)) (fun j => x (Sum.inl j.succ)) ∧
        SpatialWeakHessian (fun j => x (Sum.inl j.succ))
          (fun j k => x (Sum.inr (j, k))) := by
  simp only [physicalH2Graph, ClosedSubmodule.mem_inf, ClosedSubmodule.mem_iInf,
    ClosedSubmodule.mem_mk, LinearMap.mem_ker]
  constructor
  · rintro ⟨hG, hH⟩
    constructor
    · intro j ψ hψ hcompact
      have hzero := hG j ⟨ψ, hψ, hcompact⟩
      change weakH2Residual (Sum.inl 0) (Sum.inl j.succ) j
        ⟨ψ, hψ, hcompact⟩ x = 0 at hzero
      rw [weakH2Residual_apply] at hzero
      exact eq_neg_iff_add_eq_zero.mpr hzero
    · intro j k ψ hψ hcompact
      have hzero := hH j k ⟨ψ, hψ, hcompact⟩
      change weakH2Residual (Sum.inl j.succ) (Sum.inr (j, k)) k
        ⟨ψ, hψ, hcompact⟩ x = 0 at hzero
      rw [weakH2Residual_apply] at hzero
      exact eq_neg_iff_add_eq_zero.mpr hzero
  · rintro ⟨hG, hH⟩
    constructor
    · intro j φ
      change weakH2Residual (Sum.inl 0) (Sum.inl j.succ) j φ x = 0
      rw [weakH2Residual_apply]
      exact eq_neg_iff_add_eq_zero.mp (hG j φ.value φ.smooth φ.compact_support)
    · intro j k φ
      change weakH2Residual (Sum.inl j.succ) (Sum.inr (j, k)) k φ x = 0
      rw [weakH2Residual_apply]
      exact eq_neg_iff_add_eq_zero.mp (hH j k φ.value φ.smooth φ.compact_support)

abbrev PhysicalH2 := physicalH2Graph.toSubmodule

instance physicalH2CompleteSpace : CompleteSpace PhysicalH2 :=
  physicalH2Graph.isClosed.isComplete.completeSpace_coe

theorem physicalH2_isClosed : IsClosed (physicalH2Graph : Set H2Ambient) :=
  physicalH2Graph.isClosed

def physicalH2Velocity : PhysicalH2 →L[ℝ] SpatialL2 :=
  (PiLp.proj 2 (fun _ : H2Index => SpatialL2) (Sum.inl 0)).comp
    physicalH2Graph.toSubmodule.subtypeL

def physicalH2Gradient (j : Fin 3) : PhysicalH2 →L[ℝ] SpatialL2 :=
  (PiLp.proj 2 (fun _ : H2Index => SpatialL2) (Sum.inl j.succ)).comp
    physicalH2Graph.toSubmodule.subtypeL

def physicalH2Hessian (j k : Fin 3) : PhysicalH2 →L[ℝ] SpatialL2 :=
  (PiLp.proj 2 (fun _ : H2Index => SpatialL2) (Sum.inr (j, k))).comp
    physicalH2Graph.toSubmodule.subtypeL

theorem physicalH2_weakGradient (u : PhysicalH2) :
    SpatialWeakGradient (physicalH2Velocity u) (fun j => physicalH2Gradient j u) :=
  ((mem_physicalH2Graph_iff u.val).mp u.property).1

theorem physicalH2_weakHessian (u : PhysicalH2) :
    SpatialWeakHessian (fun j => physicalH2Gradient j u)
      (fun j k => physicalH2Hessian j k u) :=
  ((mem_physicalH2Graph_iff u.val).mp u.property).2

theorem physicalH2_norm_sq (u : PhysicalH2) :
    ‖u‖ ^ 2 = ‖physicalH2Velocity u‖ ^ 2 +
      (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) +
        ∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2 := by
  change ‖u.val‖ ^ 2 = ‖u.val (Sum.inl 0)‖ ^ 2 +
    (∑ j : Fin 3, ‖u.val (Sum.inl j.succ)‖ ^ 2) +
      ∑ j : Fin 3, ∑ k : Fin 3, ‖u.val (Sum.inr (j, k))‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Fin.sum_univ_succ,
    Fintype.sum_prod_type]

/-- The actual velocity determines every entry of the physical H2 graph. -/
theorem physicalH2Velocity_injective : Function.Injective physicalH2Velocity := by
  intro u v huv
  have hgrad : (fun j => physicalH2Gradient j u) =
      (fun j => physicalH2Gradient j v) := by
    apply spatialWeakGradient_unique (physicalH2_weakGradient u)
    rw [huv]
    exact physicalH2_weakGradient v
  have hhess : (fun j k => physicalH2Hessian j k u) =
      (fun j k => physicalH2Hessian j k v) := by
    apply spatialWeakHessian_unique (physicalH2_weakHessian u)
    rw [hgrad]
    exact physicalH2_weakHessian v
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i with
  | inl a =>
    refine Fin.cases ?_ (fun j => ?_) a
    · exact huv
    · exact congrFun hgrad j
  | inr p => exact congrFun (congrFun hhess p.1) p.2

def physicalH2OfWeakDerivatives (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) : PhysicalH2 :=
  ⟨h2Pack v G H, (mem_physicalH2Graph_iff _).mpr ⟨hG, hH⟩⟩

@[simp] theorem physicalH2OfWeakDerivatives_velocity (v : SpatialL2)
    (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    physicalH2Velocity (physicalH2OfWeakDerivatives v G H hG hH) = v := rfl

@[simp] theorem physicalH2OfWeakDerivatives_gradient (v : SpatialL2)
    (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) (j : Fin 3) :
    physicalH2Gradient j (physicalH2OfWeakDerivatives v G H hG hH) = G j := rfl

@[simp] theorem physicalH2OfWeakDerivatives_hessian (v : SpatialL2)
    (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) (j k : Fin 3) :
    physicalH2Hessian j k (physicalH2OfWeakDerivatives v G H hG hH) = H j k := rfl

private def physicalH2ToH1Fn (u : PhysicalH2) : PhysicalH1 :=
  physicalH1OfWeakGradient (physicalH2Velocity u)
    (fun j => physicalH2Gradient j u) (physicalH2_weakGradient u)

private theorem physicalH2ToH1Fn_norm_le (u : PhysicalH2) :
    ‖physicalH2ToH1Fn u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [physicalH1_norm_sq, physicalH2_norm_sq]
  change ‖physicalH2Velocity u‖ ^ 2 + (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) ≤
    ‖physicalH2Velocity u‖ ^ 2 + (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) +
      ∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The actual H2→H1 inclusion retains velocity and all first derivatives. -/
def physicalH2ToH1 : PhysicalH2 →L[ℝ] PhysicalH1 :=
  ({ toFun := physicalH2ToH1Fn
     map_add' := by
       intro u v
       apply physicalH1Velocity_injective
       simp only [physicalH2ToH1Fn, physicalH1OfWeakGradient_velocity, map_add]
     map_smul' := by
       intro r u
       apply physicalH1Velocity_injective
       simp only [physicalH2ToH1Fn, physicalH1OfWeakGradient_velocity, map_smul,
         RingHom.id_apply] } :
    PhysicalH2 →ₗ[ℝ] PhysicalH1).mkContinuous 1 (by
      intro u
      change ‖physicalH2ToH1Fn u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using physicalH2ToH1Fn_norm_le u)

@[simp] theorem physicalH2ToH1_velocity (u : PhysicalH2) :
    physicalH1Velocity (physicalH2ToH1 u) = physicalH2Velocity u := rfl

@[simp] theorem physicalH2ToH1_gradient (u : PhysicalH2) (j : Fin 3) :
    physicalH1Gradient j (physicalH2ToH1 u) = physicalH2Gradient j u := rfl

theorem norm_physicalH2ToH1_le (u : PhysicalH2) : ‖physicalH2ToH1 u‖ ≤ ‖u‖ :=
  physicalH2ToH1Fn_norm_le u

private def physicalH2GradientH1Fn (j : Fin 3) (u : PhysicalH2) : PhysicalH1 :=
  physicalH1OfWeakGradient (physicalH2Gradient j u)
    (fun k => physicalH2Hessian j k u) (physicalH2_weakHessian u j)

set_option maxHeartbeats 800000 in
private theorem physicalH2GradientH1Fn_norm_le (j : Fin 3) (u : PhysicalH2) :
    ‖physicalH2GradientH1Fn j u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [physicalH1_norm_sq, physicalH2_norm_sq]
  change ‖physicalH2Gradient j u‖ ^ 2 + (∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2) ≤
    ‖physicalH2Velocity u‖ ^ 2 + (∑ a : Fin 3, ‖physicalH2Gradient a u‖ ^ 2) +
      ∑ a : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian a k u‖ ^ 2
  have hG : ‖physicalH2Gradient j u‖ ^ 2 ≤
      ∑ a : Fin 3, ‖physicalH2Gradient a u‖ ^ 2 :=
    Finset.single_le_sum (f := fun a : Fin 3 => ‖physicalH2Gradient a u‖ ^ 2)
      (fun a _ => sq_nonneg ‖physicalH2Gradient a u‖) (Finset.mem_univ j)
  have hH : (∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2) ≤
      ∑ a : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian a k u‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun a : Fin 3 => ∑ k : Fin 3, ‖physicalH2Hessian a k u‖ ^ 2)
      (fun a _ => Finset.sum_nonneg fun k _ => sq_nonneg ‖physicalH2Hessian a k u‖)
      (Finset.mem_univ j)
  linarith [sq_nonneg ‖physicalH2Velocity u‖]

/-- Each actual first derivative is itself an element of the physical H1 graph. -/
def physicalH2GradientH1 (j : Fin 3) : PhysicalH2 →L[ℝ] PhysicalH1 :=
  ({ toFun := physicalH2GradientH1Fn j
     map_add' := by
       intro u v
       apply physicalH1Velocity_injective
       simp only [physicalH2GradientH1Fn, physicalH1OfWeakGradient_velocity, map_add]
     map_smul' := by
       intro r u
       apply physicalH1Velocity_injective
       simp only [physicalH2GradientH1Fn, physicalH1OfWeakGradient_velocity, map_smul,
         RingHom.id_apply] } :
    PhysicalH2 →ₗ[ℝ] PhysicalH1).mkContinuous 1 (by
      intro u
      change ‖physicalH2GradientH1Fn j u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using physicalH2GradientH1Fn_norm_le j u)

@[simp] theorem physicalH2GradientH1_velocity (u : PhysicalH2) (j : Fin 3) :
    physicalH1Velocity (physicalH2GradientH1 j u) = physicalH2Gradient j u := rfl

@[simp] theorem physicalH2GradientH1_gradient (u : PhysicalH2) (j k : Fin 3) :
    physicalH1Gradient k (physicalH2GradientH1 j u) = physicalH2Hessian j k u := rfl

theorem norm_physicalH2GradientH1_le (u : PhysicalH2) (j : Fin 3) :
    ‖physicalH2GradientH1 j u‖ ≤ ‖u‖ := physicalH2GradientH1Fn_norm_le j u

/-- The actual L2 Laplacian is the diagonal sum of the weak Hessian. -/
def physicalH2Laplacian : PhysicalH2 →L[ℝ] SpatialL2 :=
  ∑ j : Fin 3, physicalH2Hessian j j

theorem physicalH2Laplacian_apply (u : PhysicalH2) :
    physicalH2Laplacian u = ∑ j : Fin 3, physicalH2Hessian j j u := by
  simp only [physicalH2Laplacian, sum_apply]

/-- The diagonal L2 field is the literal native tempered-distribution Laplacian. -/
theorem physicalH2_laplacian_tempered_eq (u : PhysicalH2) :
    (complexifyL2 (physicalH2Laplacian u) : 𝓢'(Space, ComplexVector)) =
      Δ (complexifyL2 (physicalH2Velocity u) : 𝓢'(Space, ComplexVector)) := by
  have hG (j : Fin 3) :=
    H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative
      (physicalH2_weakGradient u j)
  have hH (j : Fin 3) :=
    H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative
      (physicalH2_weakHessian u j j)
  rw [physicalH2Laplacian_apply]
  have hsum : complexifyL2 (∑ j : Fin 3, physicalH2Hessian j j u) =
      ∑ j : Fin 3, complexifyL2 (physicalH2Hessian j j u) :=
    map_sum complexifyL2LI (fun j : Fin 3 => physicalH2Hessian j j u) Finset.univ
  rw [hsum, TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ)]
  change Lp.toTemperedDistributionCLM ComplexVector volume 2
    (∑ j : Fin 3, complexifyL2 (physicalH2Hessian j j u)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (complexifyL2 (physicalH2Hessian j j u) : 𝓢'(Space, ComplexVector)) = _
  rw [hH j, hG j]
  simp only [coordinateVector, EuclideanSpace.basisFun_apply]

/-- The accepted distributional spectral interface is constructed from the
actual H2 graph, rather than assumed as an extra physical hypothesis. -/
theorem physicalH2_schwartzDerivativeWitnesses (u : PhysicalH2) :
    SchwartzDerivativeWitnesses (complexifyL2 (physicalH2Velocity u))
      (fun j => complexifyL2 (physicalH2Gradient j u))
      (complexifyL2 (physicalH2Laplacian u)) := by
  constructor
  · intro j
    simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using
      H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative
        (physicalH2_weakGradient u j)
  · exact physicalH2_laplacian_tempered_eq u

/-- The solenoidal H2 graph uses the same native compact-test constraint. -/
def physicalH2SigmaGraph : ClosedSubmodule ℝ H2Ambient :=
  physicalH2Graph ⊓
    ⨅ φ : CompactSmoothScalarTest,
      let L := (solenoidalTestCLM φ).comp
        (PiLp.proj 2 (fun _ : H2Index => SpatialL2) (Sum.inl 0))
      (⟨L.ker, L.isClosed_ker⟩ : ClosedSubmodule ℝ H2Ambient)

theorem mem_physicalH2SigmaGraph_iff (x : H2Ambient) :
    x ∈ physicalH2SigmaGraph ↔
      (SpatialWeakGradient (x (Sum.inl 0)) (fun j => x (Sum.inl j.succ)) ∧
        SpatialWeakHessian (fun j => x (Sum.inl j.succ))
          (fun j k => x (Sum.inr (j, k)))) ∧ Solenoidal (x (Sum.inl 0)) := by
  simp only [physicalH2SigmaGraph, ClosedSubmodule.mem_inf, mem_physicalH2Graph_iff,
    ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_mk, LinearMap.mem_ker,
    solenoidal_iff_testCLM]
  rfl

abbrev PhysicalH2Sigma := physicalH2SigmaGraph.toSubmodule

instance physicalH2SigmaCompleteSpace : CompleteSpace PhysicalH2Sigma :=
  physicalH2SigmaGraph.isClosed.isComplete.completeSpace_coe

theorem physicalH2Sigma_isClosed : IsClosed (physicalH2SigmaGraph : Set H2Ambient) :=
  physicalH2SigmaGraph.isClosed

private def h2SubmoduleInclusionLI (p q : Submodule ℝ H2Ambient) (hpq : p ≤ q) :
    p →ₗᵢ[ℝ] q where
  toLinearMap := Submodule.inclusion hpq
  norm_map' _ := rfl

private theorem h2SubmoduleInclusionLI_val (p q : Submodule ℝ H2Ambient)
    (hpq : p ≤ q) (u : p) : (h2SubmoduleInclusionLI p q hpq u).val = u.val :=
  Submodule.coe_inclusion hpq u

private theorem physicalH2Sigma_le :
    physicalH2SigmaGraph.toSubmodule ≤ physicalH2Graph.toSubmodule := by
  intro x hx
  exact (mem_physicalH2Graph_iff x).mpr ((mem_physicalH2SigmaGraph_iff x).mp hx).1

def physicalH2SigmaToH2LI : PhysicalH2Sigma →ₗᵢ[ℝ] PhysicalH2 :=
  h2SubmoduleInclusionLI _ _ physicalH2Sigma_le

@[simp] theorem physicalH2SigmaToH2LI_val (u : PhysicalH2Sigma) :
    (physicalH2SigmaToH2LI u).val = u.val :=
  h2SubmoduleInclusionLI_val _ _ physicalH2Sigma_le u

theorem physicalH2Sigma_solenoidal (u : PhysicalH2Sigma) :
    Solenoidal (physicalH2Velocity (physicalH2SigmaToH2LI u)) := by
  change Solenoidal ((physicalH2SigmaToH2LI u).val (Sum.inl 0))
  rw [physicalH2SigmaToH2LI_val]
  exact ((mem_physicalH2SigmaGraph_iff u.val).mp u.property).2

/-- Actual Schwartz derivatives supply all nine weak Hessian entries. -/
theorem schwartz_spatialWeakHessian (a : 𝓢(Space, Space)) :
    SpatialWeakHessian (fun j => (∂_{coordinateVector j} a).toLp 2 volume)
      (fun j k => (∂_{coordinateVector k} (∂_{coordinateVector j} a)).toLp 2 volume) := by
  intro j
  exact schwartz_spatialWeakGradient (∂_{coordinateVector j} a)

def schwartzToPhysicalH2 (a : 𝓢(Space, Space)) : PhysicalH2 :=
  physicalH2OfWeakDerivatives (a.toLp 2 volume)
    (fun j => (∂_{coordinateVector j} a).toLp 2 volume)
    (fun j k => (∂_{coordinateVector k} (∂_{coordinateVector j} a)).toLp 2 volume)
    (schwartz_spatialWeakGradient a) (schwartz_spatialWeakHessian a)

@[simp] theorem schwartzToPhysicalH2_velocity (a : 𝓢(Space, Space)) :
    physicalH2Velocity (schwartzToPhysicalH2 a) = a.toLp 2 volume := rfl

@[simp] theorem schwartzToPhysicalH2_gradient (a : 𝓢(Space, Space)) (j : Fin 3) :
    physicalH2Gradient j (schwartzToPhysicalH2 a) =
      (∂_{coordinateVector j} a).toLp 2 volume := rfl

@[simp] theorem schwartzToPhysicalH2_hessian (a : 𝓢(Space, Space)) (j k : Fin 3) :
    physicalH2Hessian j k (schwartzToPhysicalH2 a) =
      (∂_{coordinateVector k} (∂_{coordinateVector j} a)).toLp 2 volume := rfl

end MethbokeAddon.QuasiFeffermanA
