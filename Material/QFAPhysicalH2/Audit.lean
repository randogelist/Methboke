import QFAPhysicalH2.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory Set FourierTransform
open scoped BigOperators FourierTransform ContDiff SchwartzMap LineDeriv Laplacian

namespace QFAPhysicalH2.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.H2Spectral
open QFA.Endpoints.Representation
open QFA.Endpoints.Agmon (ComplexVector ComplexL2 SchwartzDerivativeWitnesses)

-- Full-volume physical carriers and all thirteen separate Hilbert entries.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : H2Index = (Fin 4 ⊕ (Fin 3 × Fin 3)) := rfl
example : Fintype.card H2Index = 13 := card_H2Index
example : H2Ambient = PiLp 2 (fun _ : Fin 4 ⊕ (Fin 3 × Fin 3) =>
    Lp (EuclideanSpace ℝ (Fin 3)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := rfl

example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2) :
    h2Pack v G H = WithLp.toLp 2
      (Sum.elim (Fin.cons v G) (fun p : Fin 3 × Fin 3 => H p.1 p.2)) := rfl
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2) :
    h2Pack v G H (Sum.inl 0) = v := h2Pack_velocity v G H
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (j : Fin 3) : h2Pack v G H (Sum.inl j.succ) = G j := h2Pack_gradient v G H j
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (j k : Fin 3) : h2Pack v G H (Sum.inr (j, k)) = H j k := h2Pack_hessian v G H j k

-- Every first and second derivative uses all compact smooth real tests.
example (v : SpatialL2) (G : Fin 3 → SpatialL2) :
    SpatialWeakGradient v G ↔
      ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
          -(∫ x : Space, ψ x • G j x) := Iff.rfl
example (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2) :
    SpatialWeakHessian G H ↔
      ∀ (j k : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ)) • G j x) =
          -(∫ x : Space, ψ x • H j k x) := Iff.rfl
example (G : Fin 3 → SpatialL2) (H K : Fin 3 → Fin 3 → SpatialL2)
    (hH : ∀ (j k : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ)) • G j x) =
        -(∫ x : Space, ψ x • H j k x))
    (hK : ∀ (j k : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ)) • G j x) =
        -(∫ x : Space, ψ x • K j k x)) : H = K := spatialWeakHessian_unique hH hK

example (a b : H2Index) (k : Fin 3) (φ : CompactSmoothScalarTest) :
    weakH2Residual a b k φ =
      (compactPairingCLM (fun x => fderiv ℝ φ.value x (EuclideanSpace.single k (1 : ℝ)))
        ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
        (φ.compact_support.fderiv_apply ℝ (EuclideanSpace.single k (1 : ℝ)))).comp
          (PiLp.proj 2 (fun _ : H2Index => SpatialL2) a) +
      (compactPairingCLM φ.value φ.smooth.continuous φ.compact_support).comp
        (PiLp.proj 2 (fun _ : H2Index => SpatialL2) b) := rfl
example (a b : H2Index) (k : Fin 3) (φ : CompactSmoothScalarTest) (x : H2Ambient) :
    weakH2Residual a b k φ x =
      (∫ y : Space, fderiv ℝ φ.value y (EuclideanSpace.single k (1 : ℝ)) • x a y) +
        ∫ y : Space, φ.value y • x b y := weakH2Residual_apply a b k φ x
example : physicalH2Graph =
    (⨅ j : Fin 3, ⨅ φ : CompactSmoothScalarTest,
      (⟨(weakH2Residual (Sum.inl 0) (Sum.inl j.succ) j φ).ker,
        (weakH2Residual (Sum.inl 0) (Sum.inl j.succ) j φ).isClosed_ker⟩ :
          ClosedSubmodule ℝ H2Ambient)) ⊓
    (⨅ j : Fin 3, ⨅ k : Fin 3, ⨅ φ : CompactSmoothScalarTest,
      (⟨(weakH2Residual (Sum.inl j.succ) (Sum.inr (j, k)) k φ).ker,
        (weakH2Residual (Sum.inl j.succ) (Sum.inr (j, k)) k φ).isClosed_ker⟩ :
          ClosedSubmodule ℝ H2Ambient)) := rfl
example (x : H2Ambient) : x ∈ physicalH2Graph ↔
    (∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y : Space, fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ)) • x (Sum.inl 0) y) =
        -(∫ y : Space, ψ y • x (Sum.inl j.succ) y)) ∧
    (∀ (j k : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y : Space, fderiv ℝ ψ y (EuclideanSpace.single k (1 : ℝ)) •
        x (Sum.inl j.succ) y) = -(∫ y : Space, ψ y • x (Sum.inr (j, k)) y)) :=
  mem_physicalH2Graph_iff x
example : PhysicalH2 = physicalH2Graph.toSubmodule := rfl
example : CompleteSpace PhysicalH2 := physicalH2CompleteSpace
example : IsClosed (physicalH2Graph : Set H2Ambient) := physicalH2_isClosed

example : PhysicalH2 →L[ℝ] SpatialL2 := physicalH2Velocity
example (u : PhysicalH2) : physicalH2Velocity u = u.val (Sum.inl 0) := rfl
example (j : Fin 3) : PhysicalH2 →L[ℝ] SpatialL2 := physicalH2Gradient j
example (u : PhysicalH2) (j : Fin 3) :
    physicalH2Gradient j u = u.val (Sum.inl j.succ) := rfl
example (j k : Fin 3) : PhysicalH2 →L[ℝ] SpatialL2 := physicalH2Hessian j k
example (u : PhysicalH2) (j k : Fin 3) :
    physicalH2Hessian j k u = u.val (Sum.inr (j, k)) := rfl
example (u : PhysicalH2) :
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • physicalH2Velocity u x) =
        -(∫ x : Space, ψ x • physicalH2Gradient j u x) := physicalH2_weakGradient u
example (u : PhysicalH2) :
    ∀ (j k : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ)) •
        physicalH2Gradient j u x) =
          -(∫ x : Space, ψ x • physicalH2Hessian j k u x) := physicalH2_weakHessian u
example (u : PhysicalH2) : ‖u‖ ^ 2 = ‖physicalH2Velocity u‖ ^ 2 +
    (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) +
      ∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2 := physicalH2_norm_sq u
example : Function.Injective physicalH2Velocity := physicalH2Velocity_injective

example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) : PhysicalH2 :=
  physicalH2OfWeakDerivatives v G H hG hH
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    (physicalH2OfWeakDerivatives v G H hG hH).val = WithLp.toLp 2
      (Sum.elim (Fin.cons v G) (fun p : Fin 3 × Fin 3 => H p.1 p.2)) := rfl
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    physicalH2Velocity (physicalH2OfWeakDerivatives v G H hG hH) = v :=
  physicalH2OfWeakDerivatives_velocity v G H hG hH
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) (j : Fin 3) :
    physicalH2Gradient j (physicalH2OfWeakDerivatives v G H hG hH) = G j :=
  physicalH2OfWeakDerivatives_gradient v G H hG hH j
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) (j k : Fin 3) :
    physicalH2Hessian j k (physicalH2OfWeakDerivatives v G H hG hH) = H j k :=
  physicalH2OfWeakDerivatives_hessian v G H hG hH j k

example : PhysicalH2 →L[ℝ] PhysicalH1 := physicalH2ToH1
example (u : PhysicalH2) : (physicalH2ToH1 u).val = WithLp.toLp 2
    (Fin.cons (physicalH2Velocity u) (fun j => physicalH2Gradient j u)) := rfl
example (u : PhysicalH2) :
    physicalH1Velocity (physicalH2ToH1 u) = physicalH2Velocity u := physicalH2ToH1_velocity u
example (u : PhysicalH2) (j : Fin 3) :
    physicalH1Gradient j (physicalH2ToH1 u) = physicalH2Gradient j u := physicalH2ToH1_gradient u j
example (u : PhysicalH2) : ‖physicalH2ToH1 u‖ ≤ ‖u‖ := norm_physicalH2ToH1_le u
example (j : Fin 3) : PhysicalH2 →L[ℝ] PhysicalH1 := physicalH2GradientH1 j
example (u : PhysicalH2) (j : Fin 3) : (physicalH2GradientH1 j u).val = WithLp.toLp 2
    (Fin.cons (physicalH2Gradient j u) (fun k => physicalH2Hessian j k u)) := rfl
example (u : PhysicalH2) (j : Fin 3) :
    physicalH1Velocity (physicalH2GradientH1 j u) = physicalH2Gradient j u :=
  physicalH2GradientH1_velocity u j
example (u : PhysicalH2) (j k : Fin 3) :
    physicalH1Gradient k (physicalH2GradientH1 j u) = physicalH2Hessian j k u :=
  physicalH2GradientH1_gradient u j k
example (u : PhysicalH2) (j : Fin 3) : ‖physicalH2GradientH1 j u‖ ≤ ‖u‖ :=
  norm_physicalH2GradientH1_le u j

-- The actual L2 diagonal sum is identified with the native distributional Δ.
example : physicalH2Laplacian = ∑ j : Fin 3, physicalH2Hessian j j := rfl
example (u : PhysicalH2) : physicalH2Laplacian u = ∑ j : Fin 3, physicalH2Hessian j j u :=
  physicalH2Laplacian_apply u
example (u : PhysicalH2) :
    (complexifyL2 (physicalH2Laplacian u) : 𝓢'(Space, ComplexVector)) =
      Δ (complexifyL2 (physicalH2Velocity u) : 𝓢'(Space, ComplexVector)) :=
  physicalH2_laplacian_tempered_eq u
example (u : PhysicalH2) : SchwartzDerivativeWitnesses
    (complexifyL2 (physicalH2Velocity u))
    (fun j => complexifyL2 (physicalH2Gradient j u))
    (complexifyL2 (physicalH2Laplacian u)) := physicalH2_schwartzDerivativeWitnesses u
example (u : PhysicalH2) :
    (∀ j : Fin 3, (complexifyL2 (physicalH2Gradient j u) : 𝓢'(Space, ComplexVector)) =
      ∂_{EuclideanSpace.single j (1 : ℝ)}
        (complexifyL2 (physicalH2Velocity u) : 𝓢'(Space, ComplexVector))) ∧
    (complexifyL2 (physicalH2Laplacian u) : 𝓢'(Space, ComplexVector)) =
      Δ (complexifyL2 (physicalH2Velocity u) : 𝓢'(Space, ComplexVector)) := by
  constructor
  · intro j
    simpa only [EuclideanSpace.basisFun_apply] using
      (physicalH2_schwartzDerivativeWitnesses u).gradient_eq j
  · exact (physicalH2_schwartzDerivativeWitnesses u).laplacian_eq

-- The solenoidal restriction is the identical native compact-test condition.
example (v : SpatialL2) : Solenoidal v ↔
    ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun x : Space => inner ℝ (v x)
        (WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))))) volume ∧
      (∫ x : Space, inner ℝ (v x)
        (WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))))) = 0 := Iff.rfl
example : physicalH2SigmaGraph = physicalH2Graph ⊓
    ⨅ φ : CompactSmoothScalarTest,
      let L := (solenoidalTestCLM φ).comp
        (PiLp.proj 2 (fun _ : H2Index => SpatialL2) (Sum.inl 0))
      (⟨L.ker, L.isClosed_ker⟩ : ClosedSubmodule ℝ H2Ambient) := rfl
example (x : H2Ambient) : x ∈ physicalH2SigmaGraph ↔
    (SpatialWeakGradient (x (Sum.inl 0)) (fun j => x (Sum.inl j.succ)) ∧
      SpatialWeakHessian (fun j => x (Sum.inl j.succ))
        (fun j k => x (Sum.inr (j, k)))) ∧ Solenoidal (x (Sum.inl 0)) :=
  mem_physicalH2SigmaGraph_iff x
example : PhysicalH2Sigma = physicalH2SigmaGraph.toSubmodule := rfl
example : CompleteSpace PhysicalH2Sigma := physicalH2SigmaCompleteSpace
example : IsClosed (physicalH2SigmaGraph : Set H2Ambient) := physicalH2Sigma_isClosed
example : PhysicalH2Sigma →ₗᵢ[ℝ] PhysicalH2 := physicalH2SigmaToH2LI
example (u : PhysicalH2Sigma) : (physicalH2SigmaToH2LI u).val = u.val :=
  physicalH2SigmaToH2LI_val u
example (u : PhysicalH2Sigma) :
    Solenoidal (physicalH2Velocity (physicalH2SigmaToH2LI u)) := physicalH2Sigma_solenoidal u

example (a : 𝓢(Space, Space)) :
    SpatialWeakHessian (fun j => (∂_{EuclideanSpace.single j (1 : ℝ)} a).toLp 2 volume)
      (fun j k => (∂_{EuclideanSpace.single k (1 : ℝ)}
        (∂_{EuclideanSpace.single j (1 : ℝ)} a)).toLp 2 volume) := schwartz_spatialWeakHessian a
example (a : 𝓢(Space, Space)) : PhysicalH2 := schwartzToPhysicalH2 a
example (a : 𝓢(Space, Space)) : (schwartzToPhysicalH2 a).val = WithLp.toLp 2
    (Sum.elim (Fin.cons (a.toLp 2 volume)
      (fun j => (∂_{EuclideanSpace.single j (1 : ℝ)} a).toLp 2 volume))
      (fun p : Fin 3 × Fin 3 => (∂_{EuclideanSpace.single p.2 (1 : ℝ)}
        (∂_{EuclideanSpace.single p.1 (1 : ℝ)} a)).toLp 2 volume)) := rfl
example (a : 𝓢(Space, Space)) : physicalH2Velocity (schwartzToPhysicalH2 a) = a.toLp 2 volume :=
  schwartzToPhysicalH2_velocity a
example (a : 𝓢(Space, Space)) (j : Fin 3) :
    physicalH2Gradient j (schwartzToPhysicalH2 a) =
      (∂_{EuclideanSpace.single j (1 : ℝ)} a).toLp 2 volume := schwartzToPhysicalH2_gradient a j
example (a : 𝓢(Space, Space)) (j k : Fin 3) :
    physicalH2Hessian j k (schwartzToPhysicalH2 a) =
      (∂_{EuclideanSpace.single k (1 : ℝ)}
        (∂_{EuclideanSpace.single j (1 : ℝ)} a)).toLp 2 volume := schwartzToPhysicalH2_hessian a j k

-- The second-derivative multiplier, symmetry, density and norms are outputs.
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    ∀ᵐ ξ : Space ∂volume, ∀ j k : Fin 3,
      (𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ =
        (((-((2 * Real.pi) ^ 2) * ξ j * ξ k : ℝ) : ℂ)) •
          (𝓕 (complexifyL2 v) : ComplexL2) ξ := spatialWeakHessian_fourier_ae hG hH
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) (j k : Fin 3) :
    H j k = H k j := spatialWeakHessian_symmetric hG hH j k
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    (fun ξ : Space => ∑ j : Fin 3, ∑ k : Fin 3,
      ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2) =ᵐ[volume]
        (fun ξ : Space => (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
          ‖(𝓕 (complexifyL2 v) : ComplexL2) ξ‖ ^ 2) := spatialWeakHessian_fourier_norm_ae hG hH
example (u : PhysicalH2) : ∀ᵐ ξ : Space ∂volume, ∀ j k : Fin 3,
    (𝓕 (complexifyL2 (physicalH2Hessian j k u)) : ComplexL2) ξ =
      (((-((2 * Real.pi) ^ 2) * ξ j * ξ k : ℝ) : ℂ)) •
        (𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ := physicalH2_hessian_fourier_ae u
example (u : PhysicalH2) (j k : Fin 3) :
    physicalH2Hessian j k u = physicalH2Hessian k j u := physicalH2_hessian_symmetric u j k
example (u : PhysicalH2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (physicalH2Laplacian u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        ((-((2 * Real.pi) ^ 2) : ℂ) * (‖ξ‖ ^ 2 : ℂ)) •
          (𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ) := physicalH2_laplacian_fourier_ae u
example (u : PhysicalH2) :
    Integrable (fun ξ : Space => (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) volume :=
  physicalH2_fourier_laplacian_integrable u
example (u : PhysicalH2) : ‖physicalH2Laplacian u‖ ^ 2 =
    ∫ ξ : Space, (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2 :=
  physicalH2_laplacian_norm_sq_eq_fourier u
example (u : PhysicalH2) :
    (∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2) = ‖physicalH2Laplacian u‖ ^ 2 :=
  physicalH2_hessian_norm_sq_eq_laplacian u
example (u : PhysicalH2) : ‖u‖ ^ 2 = ‖physicalH2Velocity u‖ ^ 2 +
    (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) + ‖physicalH2Laplacian u‖ ^ 2 :=
  physicalH2_norm_sq_eq_laplacian u
example (u : PhysicalH2) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) volume :=
  physicalH2_weighted_fourier_integrable u
example (u : PhysicalH2) : ‖physicalH2Laplacian u‖ ^ 2 = (2 * Real.pi) ^ 4 *
    (∫ ξ : Space, ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  physicalH2_laplacian_eq_fourier_weighted u
example (u : PhysicalH2) : ‖u‖ ^ 2 =
    (∫ ξ : Space, ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) +
    (4 * Real.pi ^ 2) * (∫ ξ : Space, ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) +
    (2 * Real.pi) ^ 4 * (∫ ξ : Space, ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) := physicalH2_norm_sq_eq_fourier u

end QFAPhysicalH2.ExpectedTypes

-- Ordered exact-type and named axiom reports.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Index"
#check @MethbokeAddon.QuasiFeffermanA.H2Index
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Index"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Index"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Index
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Index"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.card_H2Index"
#check @MethbokeAddon.QuasiFeffermanA.card_H2Index
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.card_H2Index"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.card_H2Index"
#print axioms MethbokeAddon.QuasiFeffermanA.card_H2Index
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.card_H2Index"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Ambient"
#check @MethbokeAddon.QuasiFeffermanA.H2Ambient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Ambient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Ambient"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Ambient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Ambient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack"
#check @MethbokeAddon.QuasiFeffermanA.h2Pack
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h2Pack"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack"
#print axioms MethbokeAddon.QuasiFeffermanA.h2Pack
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h2Pack"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack_velocity"
#check @MethbokeAddon.QuasiFeffermanA.h2Pack_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h2Pack_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.h2Pack_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h2Pack_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack_gradient"
#check @MethbokeAddon.QuasiFeffermanA.h2Pack_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h2Pack_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.h2Pack_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h2Pack_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack_hessian"
#check @MethbokeAddon.QuasiFeffermanA.h2Pack_hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h2Pack_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h2Pack_hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.h2Pack_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h2Pack_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SpatialWeakHessian"
#check @MethbokeAddon.QuasiFeffermanA.SpatialWeakHessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SpatialWeakHessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SpatialWeakHessian"
#print axioms MethbokeAddon.QuasiFeffermanA.SpatialWeakHessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SpatialWeakHessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.spatialWeakHessian_unique"
#check @MethbokeAddon.QuasiFeffermanA.spatialWeakHessian_unique
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.spatialWeakHessian_unique"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.spatialWeakHessian_unique"
#print axioms MethbokeAddon.QuasiFeffermanA.spatialWeakHessian_unique
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.spatialWeakHessian_unique"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.weakH2Residual"
#check @MethbokeAddon.QuasiFeffermanA.weakH2Residual
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.weakH2Residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.weakH2Residual"
#print axioms MethbokeAddon.QuasiFeffermanA.weakH2Residual
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.weakH2Residual"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.weakH2Residual_apply"
#check @MethbokeAddon.QuasiFeffermanA.weakH2Residual_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.weakH2Residual_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.weakH2Residual_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.weakH2Residual_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.weakH2Residual_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Graph"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Graph
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Graph"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Graph"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Graph
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Graph"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH2Graph_iff"
#check @MethbokeAddon.QuasiFeffermanA.mem_physicalH2Graph_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH2Graph_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH2Graph_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.mem_physicalH2Graph_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH2Graph_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH2"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH2"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2CompleteSpace"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2CompleteSpace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2CompleteSpace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2CompleteSpace"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2CompleteSpace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2CompleteSpace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_isClosed"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_isClosed
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_isClosed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_isClosed"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_isClosed
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_isClosed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Hessian"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_weakGradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_weakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_weakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_weakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_weakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_weakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_weakHessian"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_weakHessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_weakHessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_weakHessian"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_weakHessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_weakHessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity_injective"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Velocity_injective
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity_injective"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity_injective"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Velocity_injective
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Velocity_injective"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_hessian"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2OfWeakDerivatives_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2ToH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2ToH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2ToH1_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH2ToH1_le"
#check @MethbokeAddon.QuasiFeffermanA.norm_physicalH2ToH1_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH2ToH1_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH2ToH1_le"
#print axioms MethbokeAddon.QuasiFeffermanA.norm_physicalH2ToH1_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH2ToH1_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2GradientH1_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH2GradientH1_le"
#check @MethbokeAddon.QuasiFeffermanA.norm_physicalH2GradientH1_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH2GradientH1_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH2GradientH1_le"
#print axioms MethbokeAddon.QuasiFeffermanA.norm_physicalH2GradientH1_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH2GradientH1_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian_apply"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Laplacian_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_laplacian_tempered_eq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_laplacian_tempered_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_laplacian_tempered_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_laplacian_tempered_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_laplacian_tempered_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_laplacian_tempered_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_schwartzDerivativeWitnesses"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_schwartzDerivativeWitnesses
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_schwartzDerivativeWitnesses"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_schwartzDerivativeWitnesses"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_schwartzDerivativeWitnesses
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_schwartzDerivativeWitnesses"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaGraph"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2SigmaGraph
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaGraph"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaGraph"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2SigmaGraph
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaGraph"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH2SigmaGraph_iff"
#check @MethbokeAddon.QuasiFeffermanA.mem_physicalH2SigmaGraph_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH2SigmaGraph_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH2SigmaGraph_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.mem_physicalH2SigmaGraph_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH2SigmaGraph_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH2Sigma"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH2Sigma
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH2Sigma"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH2Sigma"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH2Sigma
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH2Sigma"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaCompleteSpace"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2SigmaCompleteSpace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaCompleteSpace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaCompleteSpace"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2SigmaCompleteSpace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaCompleteSpace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_isClosed"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_isClosed
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_isClosed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_isClosed"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_isClosed
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_isClosed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI_val"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI_val
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI_val"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI_val"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI_val
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2SigmaToH2LI_val"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2Sigma_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakHessian"
#check @MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakHessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakHessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakHessian"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakHessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakHessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_velocity"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_gradient"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_hessian"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_symmetric"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_symmetric
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_symmetric"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_symmetric"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_symmetric
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_symmetric"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_norm_ae"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_norm_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_norm_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_norm_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_norm_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.spatialWeakHessian_fourier_norm_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_symmetric"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_symmetric
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_symmetric"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_symmetric"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_symmetric
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_symmetric"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_fourier_laplacian_integrable"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_fourier_laplacian_integrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_fourier_laplacian_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_fourier_laplacian_integrable"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_fourier_laplacian_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_fourier_laplacian_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_laplacian"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_laplacian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_laplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_laplacian"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_laplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_laplacian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_weighted_fourier_integrable"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_weighted_fourier_integrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_weighted_fourier_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_weighted_fourier_integrable"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_weighted_fourier_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_weighted_fourier_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_eq_fourier_weighted"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_eq_fourier_weighted
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_eq_fourier_weighted"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_eq_fourier_weighted"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_eq_fourier_weighted
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_laplacian_eq_fourier_weighted"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H2Spectral.physicalH2_norm_sq_eq_fourier"
