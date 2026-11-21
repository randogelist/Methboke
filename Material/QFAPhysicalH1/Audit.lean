import QFAPhysicalH1.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology SchwartzMap LineDeriv
open MethbokeAddon.QuasiFeffermanA
open QFA.Endpoints.Representation

namespace PhysicalH1ExpectedTypes

-- Explicit consumers: every argument and conclusion is written independently.
example : ∀ {v G H : SpatialL2} {e : MethbokeAddon.QuasiFeffermanA.Space},
    RealTestWeakDirectionalDerivative v G e →
    RealTestWeakDirectionalDerivative v H e → G = H :=
  @realTestWeakDirectionalDerivative_unique

example : ∀ {v : SpatialL2} {G H : Fin 3 → SpatialL2},
    SpatialWeakGradient v G → SpatialWeakGradient v H → G = H :=
  @spatialWeakGradient_unique

example : ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), Continuous ψ → HasCompactSupport ψ →
    SpatialL2 →L[ℝ] MethbokeAddon.QuasiFeffermanA.Space := @compactPairingCLM

example : ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (v : SpatialL2), compactPairingCLM ψ hψ hc v = ∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • v x :=
  @compactPairingCLM_apply

example : Type := CompactSmoothScalarTest

example : H1Ambient = PiLp 2 (fun _ : Fin 4 =>
    Lp (EuclideanSpace ℝ (Fin 3)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := rfl

example : SpatialL2 → (Fin 3 → SpatialL2) → H1Ambient := @h1Pack

example : ∀ (v : SpatialL2) (G : Fin 3 → SpatialL2), h1Pack v G 0 = v :=
  @h1Pack_zero

example : ∀ (v : SpatialL2) (G : Fin 3 → SpatialL2) (j : Fin 3),
    h1Pack v G j.succ = G j := @h1Pack_succ

example : Fin 3 → CompactSmoothScalarTest → H1Ambient →L[ℝ] MethbokeAddon.QuasiFeffermanA.Space :=
  @weakGradientResidual

example : ∀ (j : Fin 3) (φ : CompactSmoothScalarTest) (x : H1Ambient),
    weakGradientResidual j φ x =
      (∫ y : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ φ.value y (coordinateVector j) • x 0 y) +
      ∫ y : MethbokeAddon.QuasiFeffermanA.Space, φ.value y • x j.succ y := @weakGradientResidual_apply

example : ClosedSubmodule ℝ H1Ambient := physicalH1Graph

example : ∀ x : H1Ambient,
    x ∈ physicalH1Graph ↔ SpatialWeakGradient (x 0) (fun j => x j.succ) :=
  @mem_physicalH1Graph_iff

example : PhysicalH1 = physicalH1Graph.toSubmodule := rfl

example : CompleteSpace PhysicalH1 := physicalH1CompleteSpace

example : IsClosed (physicalH1Graph : Set H1Ambient) := physicalH1_isClosed

example : PhysicalH1 →L[ℝ] SpatialL2 := physicalH1Velocity

example : Fin 3 → PhysicalH1 →L[ℝ] SpatialL2 := physicalH1Gradient

example : ∀ u : PhysicalH1,
    SpatialWeakGradient (physicalH1Velocity u) (fun j => physicalH1Gradient j u) :=
  @physicalH1_weakGradient

example : ∀ u : PhysicalH1, ‖u‖ ^ 2 = ‖physicalH1Velocity u‖ ^ 2 +
    ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 := @physicalH1_norm_sq

example : Function.Injective physicalH1Velocity := physicalH1Velocity_injective

example : ∀ (v : SpatialL2) (G : Fin 3 → SpatialL2),
    SpatialWeakGradient v G → PhysicalH1 := @physicalH1OfWeakGradient

example : ∀ (v : SpatialL2) (G : Fin 3 → SpatialL2) (h : SpatialWeakGradient v G),
    physicalH1Velocity (physicalH1OfWeakGradient v G h) = v :=
  @physicalH1OfWeakGradient_velocity

example : ∀ (v : SpatialL2) (G : Fin 3 → SpatialL2) (h : SpatialWeakGradient v G)
    (j : Fin 3), physicalH1Gradient j (physicalH1OfWeakGradient v G h) = G j :=
  @physicalH1OfWeakGradient_gradient

example : ∀ {ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ}, ContDiff ℝ ∞ ψ → Continuous (scalarGradient ψ) :=
  @scalarGradient_continuous

example : ∀ {ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ}, HasCompactSupport ψ →
    HasCompactSupport (scalarGradient ψ) := @scalarGradient_hasCompactSupport

example : CompactSmoothScalarTest → SpatialL2 := scalarTestGradientL2

example : ∀ φ : CompactSmoothScalarTest,
    scalarTestGradientL2 φ =ᵐ[volume] scalarGradient φ.value :=
  @scalarTestGradientL2_ae

example : CompactSmoothScalarTest → SpatialL2 →L[ℝ] ℝ := solenoidalTestCLM

example : ∀ (φ : CompactSmoothScalarTest) (v : SpatialL2),
    solenoidalTestCLM φ v = ∫ x : MethbokeAddon.QuasiFeffermanA.Space, inner ℝ (v x) (scalarGradient φ.value x) :=
  @solenoidalTestCLM_apply

example : ∀ (φ : CompactSmoothScalarTest) (v : SpatialL2),
    Integrable (fun x : MethbokeAddon.QuasiFeffermanA.Space => inner ℝ (v x) (scalarGradient φ.value x)) volume :=
  @integrable_solenoidalTest

example : ∀ v : SpatialL2,
    Solenoidal v ↔ ∀ φ : CompactSmoothScalarTest, solenoidalTestCLM φ v = 0 :=
  @solenoidal_iff_testCLM

example : ClosedSubmodule ℝ H1Ambient := physicalH1SigmaGraph

example : ∀ x : H1Ambient, x ∈ physicalH1SigmaGraph ↔
    SpatialWeakGradient (x 0) (fun j => x j.succ) ∧ Solenoidal (x 0) :=
  @mem_physicalH1SigmaGraph_iff

example : PhysicalH1Sigma = physicalH1SigmaGraph.toSubmodule := rfl

example : CompleteSpace PhysicalH1Sigma := physicalH1SigmaCompleteSpace

example : IsClosed (physicalH1SigmaGraph : Set H1Ambient) := physicalH1Sigma_isClosed

example : ∀ u : PhysicalH1Sigma,
    SpatialWeakGradient (u.val 0) (fun j => u.val j.succ) :=
  @physicalH1Sigma_weakGradient

example : ∀ u : PhysicalH1Sigma, Solenoidal (u.val 0) := @physicalH1Sigma_solenoidal

example : ∀ u : PhysicalH1Sigma,
    ‖u‖ ^ 2 = ‖u.val 0‖ ^ 2 + ∑ j : Fin 3, ‖u.val j.succ‖ ^ 2 :=
  @physicalH1Sigma_norm_sq

example : Function.Injective (fun u : PhysicalH1Sigma => u.val 0) :=
  physicalH1Sigma_velocity_injective

example : ∀ a : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space), SpatialWeakGradient (a.toLp 2 volume)
    (fun j => (∂_{coordinateVector j} a).toLp 2 volume) := @schwartz_spatialWeakGradient

example : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space) → PhysicalH1 := schwartzToPhysicalH1

example : ∀ a : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space),
    physicalH1Velocity (schwartzToPhysicalH1 a) = a.toLp 2 volume :=
  @schwartzToPhysicalH1_velocity

example : ∀ a : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space), Solenoidal (a.toLp 2 volume) → PhysicalH1Sigma :=
  @schwartzToPhysicalH1Sigma

example : ∀ (a : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space)) (hsol : Solenoidal (a.toLp 2 volume)),
    (schwartzToPhysicalH1Sigma a hsol).val 0 = a.toLp 2 volume :=
  @schwartzToPhysicalH1Sigma_velocity

-- Literal physical-contract checks. These explicitly retain full R3 volume,
-- all compact real tests, actual derivatives, and the physical norm.
example (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    CompactSmoothScalarTest := ⟨ψ, hψ, hc⟩

example (φ : CompactSmoothScalarTest) :
    ContDiff ℝ ∞ φ.value ∧ HasCompactSupport φ.value :=
  ⟨φ.smooth, φ.compact_support⟩

example (x : H1Ambient) : x ∈ physicalH1Graph ↔
    ∀ (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ)) • x 0 y) =
      -(∫ y : MethbokeAddon.QuasiFeffermanA.Space, ψ y • x j.succ y) := mem_physicalH1Graph_iff x

example (x : H1Ambient) : x ∈ physicalH1SigmaGraph ↔
    (∀ (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ)) • x 0 y) =
      -(∫ y : MethbokeAddon.QuasiFeffermanA.Space, ψ y • x j.succ y)) ∧
    (∀ ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun y : MethbokeAddon.QuasiFeffermanA.Space => inner ℝ (x 0 y)
        (WithLp.toLp 2 (fun j : Fin 3 =>
          fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ))))) volume ∧
      (∫ y : MethbokeAddon.QuasiFeffermanA.Space, inner ℝ (x 0 y)
        (WithLp.toLp 2 (fun j : Fin 3 =>
          fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ))))) = 0) :=
  mem_physicalH1SigmaGraph_iff x

example : InnerProductSpace ℝ PhysicalH1 := inferInstance
example : InnerProductSpace ℝ PhysicalH1Sigma := inferInstance
example : CompleteSpace H1Ambient := inferInstance

example (a : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space)) (j : Fin 3) :
    physicalH1Gradient j (schwartzToPhysicalH1 a) =
      (∂_{EuclideanSpace.single j (1 : ℝ)} a).toLp 2 volume := rfl

example (a : 𝓢(MethbokeAddon.QuasiFeffermanA.Space, MethbokeAddon.QuasiFeffermanA.Space)) (hsol : Solenoidal (a.toLp 2 volume)) :
    ‖schwartzToPhysicalH1Sigma a hsol‖ ^ 2 =
      ‖a.toLp 2 volume‖ ^ 2 +
      ∑ j : Fin 3, ‖(∂_{EuclideanSpace.single j (1 : ℝ)} a).toLp 2 volume‖ ^ 2 :=
  physicalH1Sigma_norm_sq (schwartzToPhysicalH1Sigma a hsol)

end PhysicalH1ExpectedTypes

end

-- NAMED REPORTS: generated text, executed only by authorized external CI.
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.realTestWeakDirectionalDerivative_unique"
#check @MethbokeAddon.QuasiFeffermanA.realTestWeakDirectionalDerivative_unique
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.realTestWeakDirectionalDerivative_unique"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.realTestWeakDirectionalDerivative_unique"
#print axioms MethbokeAddon.QuasiFeffermanA.realTestWeakDirectionalDerivative_unique
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.realTestWeakDirectionalDerivative_unique"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_unique"
#check @MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_unique
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_unique"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_unique"
#print axioms MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_unique
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.spatialWeakGradient_unique"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.compactPairingCLM"
#check @MethbokeAddon.QuasiFeffermanA.compactPairingCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.compactPairingCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.compactPairingCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.compactPairingCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.compactPairingCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.compactPairingCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.compactPairingCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.compactPairingCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.compactPairingCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.compactPairingCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.compactPairingCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.CompactSmoothScalarTest"
#check @MethbokeAddon.QuasiFeffermanA.CompactSmoothScalarTest
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.CompactSmoothScalarTest"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.CompactSmoothScalarTest"
#print axioms MethbokeAddon.QuasiFeffermanA.CompactSmoothScalarTest
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.CompactSmoothScalarTest"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Ambient"
#check @MethbokeAddon.QuasiFeffermanA.H1Ambient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Ambient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Ambient"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Ambient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Ambient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h1Pack"
#check @MethbokeAddon.QuasiFeffermanA.h1Pack
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h1Pack"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h1Pack"
#print axioms MethbokeAddon.QuasiFeffermanA.h1Pack
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h1Pack"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h1Pack_zero"
#check @MethbokeAddon.QuasiFeffermanA.h1Pack_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h1Pack_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h1Pack_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.h1Pack_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h1Pack_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.h1Pack_succ"
#check @MethbokeAddon.QuasiFeffermanA.h1Pack_succ
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.h1Pack_succ"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.h1Pack_succ"
#print axioms MethbokeAddon.QuasiFeffermanA.h1Pack_succ
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.h1Pack_succ"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.weakGradientResidual"
#check @MethbokeAddon.QuasiFeffermanA.weakGradientResidual
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.weakGradientResidual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.weakGradientResidual"
#print axioms MethbokeAddon.QuasiFeffermanA.weakGradientResidual
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.weakGradientResidual"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.weakGradientResidual_apply"
#check @MethbokeAddon.QuasiFeffermanA.weakGradientResidual_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.weakGradientResidual_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.weakGradientResidual_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.weakGradientResidual_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.weakGradientResidual_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Graph"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Graph
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Graph"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Graph"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Graph
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Graph"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH1Graph_iff"
#check @MethbokeAddon.QuasiFeffermanA.mem_physicalH1Graph_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH1Graph_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH1Graph_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.mem_physicalH1Graph_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH1Graph_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1CompleteSpace"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1CompleteSpace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1CompleteSpace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1CompleteSpace"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1CompleteSpace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1CompleteSpace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_isClosed"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_isClosed
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_isClosed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_isClosed"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_isClosed
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_isClosed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_weakGradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_weakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_weakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_weakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_weakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_weakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity_injective"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Velocity_injective
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity_injective"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity_injective"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Velocity_injective
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Velocity_injective"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1OfWeakGradient_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarGradient_continuous"
#check @MethbokeAddon.QuasiFeffermanA.scalarGradient_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.scalarGradient_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarGradient_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.scalarGradient_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.scalarGradient_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarGradient_hasCompactSupport"
#check @MethbokeAddon.QuasiFeffermanA.scalarGradient_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.scalarGradient_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarGradient_hasCompactSupport"
#print axioms MethbokeAddon.QuasiFeffermanA.scalarGradient_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.scalarGradient_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2"
#check @MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2"
#print axioms MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2_ae"
#check @MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.scalarTestGradientL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM"
#check @MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.solenoidalTestCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.integrable_solenoidalTest"
#check @MethbokeAddon.QuasiFeffermanA.integrable_solenoidalTest
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.integrable_solenoidalTest"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.integrable_solenoidalTest"
#print axioms MethbokeAddon.QuasiFeffermanA.integrable_solenoidalTest
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.integrable_solenoidalTest"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.solenoidal_iff_testCLM"
#check @MethbokeAddon.QuasiFeffermanA.solenoidal_iff_testCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.solenoidal_iff_testCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.solenoidal_iff_testCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.solenoidal_iff_testCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.solenoidal_iff_testCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaGraph"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaGraph
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaGraph"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaGraph"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaGraph
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaGraph"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH1SigmaGraph_iff"
#check @MethbokeAddon.QuasiFeffermanA.mem_physicalH1SigmaGraph_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH1SigmaGraph_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalH1SigmaGraph_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.mem_physicalH1SigmaGraph_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.mem_physicalH1SigmaGraph_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Sigma"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Sigma
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Sigma"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Sigma"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Sigma
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Sigma"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaCompleteSpace"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaCompleteSpace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaCompleteSpace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaCompleteSpace"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaCompleteSpace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaCompleteSpace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_isClosed"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_isClosed
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_isClosed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_isClosed"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_isClosed
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_isClosed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_weakGradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_weakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_weakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_weakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_weakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_weakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_velocity_injective"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_velocity_injective
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_velocity_injective"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_velocity_injective"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_velocity_injective
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Sigma_velocity_injective"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakGradient"
#check @MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartz_spatialWeakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1_velocity"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma_velocity"
#check @MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.schwartzToPhysicalH1Sigma_velocity"
