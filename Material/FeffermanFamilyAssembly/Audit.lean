import FeffermanFamilyAssembly.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent full consumer statements for the growth/transport/native-assembly
layer. Complete ordered type and axiom reports must be run freshly by the
existing authorized external workflow. No seed existence is assumed globally. -/

open Filter Set
open scoped Topology

namespace MethbokeAddon.FeffermanFamily.GrowthSequenceAudit

universe u v
variable {X : Type u} {E : Type v}
variable [PseudoMetricSpace X] [NormedAddCommGroup E]

example (U : ℝ → X → E) (T : ℝ) :
    SpeedUnboundedAt U T =
      (∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
        ∃ t : ℝ, ∃ x : X,
          t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ M < ‖U t x‖) := rfl

example {U : ℝ → X → E} {a : X} {T : ℝ}
    (hU : LocalVelocityBlowup U a T) : SpeedUnboundedAt U T :=
  LocalVelocityBlowup.speedUnboundedAt hU

example {U : ℝ → X → E} {T : ℝ}
    (hU : SpeedUnboundedAt U T) : 0 < T :=
  SpeedUnboundedAt.terminal_pos hU

example {U : ℝ → X → E} {T : ℝ} (hU : SpeedUnboundedAt U T) :
    ∃ t : ℕ → ℝ, ∃ x : ℕ → X,
      (∀ n, 0 < t n ∧ t n < T) ∧
      (∀ n, T - t n < 1 / ((n : ℝ) + 1)) ∧
      (∀ n, (n : ℝ) + 1 < ‖U (t n) (x n)‖) ∧
      Tendsto t atTop (𝓝 T) ∧
      Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop :=
  SpeedUnboundedAt.exists_growth_sequence hU

example {U : ℝ → X → E} {T : ℝ} (hU : SpeedUnboundedAt U T)
    (K : Set X)
    (hzero : ∀ t, 0 < t → t < T → ∀ x, x ∉ K → U t x = 0) :
    ∃ t : ℕ → ℝ, ∃ x : ℕ → X,
      (∀ n, 0 < t n ∧ t n < T) ∧
      (∀ n, x n ∈ K) ∧
      (∀ n, T - t n < 1 / ((n : ℝ) + 1)) ∧
      (∀ n, (n : ℝ) + 1 < ‖U (t n) (x n)‖) ∧
      Tendsto t atTop (𝓝 T) ∧
      Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop :=
  SpeedUnboundedAt.exists_growth_sequence_in_carrier hU K hzero

example {U : ℝ → X → E} {T : ℝ} (hU : SpeedUnboundedAt U T)
    (K : Set X) (hK : IsCompact K)
    (hzero : ∀ t, 0 < t → t < T → ∀ x, x ∉ K → U t x = 0) :
    ∃ a ∈ K, LocalVelocityBlowup U a T :=
  SpeedUnboundedAt.exists_localVelocityBlowup hU K hK hzero

end MethbokeAddon.FeffermanFamily.GrowthSequenceAudit

namespace FeffermanFamilyAssembly.CopyTypeChecks

open MethbokeAddon.FeffermanFamily

universe u_copy v_copy

example {X : Type u_copy} {E : Type v_copy}
    [NormedAddCommGroup X] [NormedAddCommGroup E]
    {U : ℝ → X → E} {b : X} {T : ℝ}
    (hU : LocalVelocityBlowup U b T) (a : X) :
    LocalVelocityBlowup (fun t x => U t (x - a)) (b + a) T :=
  LocalVelocityBlowup.spatial_translate hU a

example {X : Type u_copy} {E : Type v_copy}
    [NormedAddCommGroup X] [NormedAddCommGroup E]
    {U : ℝ → X → E} {b : X} {T : ℝ}
    (hU : LocalVelocityBlowup U b T) :
    LocalVelocityBlowup (fun t x => U t (x + b)) 0 T :=
  LocalVelocityBlowup.recenter hU

example {X : Type u_copy} {E : Type v_copy}
    [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : ℝ → X → E} {a : X} {T : ℝ}
    (hU : LocalVelocityBlowup U a T) (c : ℝ) (hc : 0 < c) :
    LocalVelocityBlowup (fun t x => c • U t x) a T :=
  LocalVelocityBlowup.positive_smul hU c hc

example {X : Type u_copy} {E : Type v_copy}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {U : ℝ → X → E} {T : ℝ}
    (hU : LocalVelocityBlowup U 0 T) (c : ℝ) (hc : 0 < c) :
    LocalVelocityBlowup (fun t x => U t (c • x)) 0 T :=
  LocalVelocityBlowup.positive_spatial_scale hU c hc

example {X : Type u_copy} {E : Type v_copy}
    [PseudoMetricSpace X] [NormedAddCommGroup E]
    {U : ℝ → X → E} {a : X}
    (hU : LocalVelocityBlowup U a 1) (c : ℝ) (hc : 1 ≤ c) :
    LocalVelocityBlowup (fun t x => U (1 + c * (t - 1)) x) a 1 :=
  LocalVelocityBlowup.time_compress_at_one hU c hc

example {X : Type u_copy} {E : Type v_copy}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : ℝ → X → E}
    (hU : LocalVelocityBlowup U 0 1) (λ : ℝ) (hλ : 1 < λ) (a : X) :
    LocalVelocityBlowup
      (fun t x => λ • U (1 + λ ^ 2 * (t - 1)) (λ • (x - a))) a 1 :=
  LocalVelocityBlowup.parabolic_copy hU λ hλ a

end FeffermanFamilyAssembly.CopyTypeChecks

open Set Filter SingularClosure
open scoped BigOperators Topology

namespace MethbokeAddon.FeffermanFamily.AssemblyTypeChecks

-- Independent consumer statements use explicit quantified input types.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → Vec → E) (t : ℝ) (x : Vec)
    (h : (fun z : ℝ × Vec => f z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => g z.1 z.2)) :
    fderiv ℝ (f t) x = fderiv ℝ (g t) x :=
  nativeSpatialFDeriv_congr h

example (u v : Velocity) (t : ℝ) (x : Vec)
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => v z.1 z.2)) :
    timeDerivative u t x = timeDerivative v t x :=
  nativeTimeDerivative_congr h

example (u v : Velocity) (t : ℝ) (x : Vec) (i : Fin 3)
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => v z.1 z.2)) :
    coordinateDerivative (u t) i x = coordinateDerivative (v t) i x :=
  nativeCoordinateDerivative_congr h i

example (u v : Velocity) (t : ℝ) (x : Vec)
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => v z.1 z.2)) :
    divergence (u t) x = divergence (v t) x :=
  nativeDivergence_congr h

example (p q : Pressure) (t : ℝ) (x : Vec)
    (h : (fun z : ℝ × Vec => p z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => q z.1 z.2)) :
    SingularClosure.gradient (p t) x = SingularClosure.gradient (q t) x :=
  nativeGradient_congr h

example (u v : Velocity) (t : ℝ) (x : Vec)
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => v z.1 z.2)) :
    laplacian (u t) x = laplacian (v t) x :=
  nativeLaplacian_congr h

example (u v : Velocity) (t : ℝ) (x : Vec)
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => v z.1 z.2)) :
    convection (u t) x = convection (v t) x :=
  nativeConvection_congr h

example (ν : ℝ) (u v F G : Velocity) (p q : Pressure) (t : ℝ) (x : Vec)
    (hu : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => v z.1 z.2))
    (hp : (fun z : ℝ × Vec => p z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => q z.1 z.2))
    (hF : (fun z : ℝ × Vec => F z.1 z.2) =ᶠ[𝓝 (t,x)]
      (fun z => G z.1 z.2)) :
    (timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x + F t x) ↔
    (timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
      ν • laplacian (v t) x + G t x) :=
  nativeForcedEquation_congr ν hu hp hF

example (ν t : ℝ) (x : Vec) :
    timeDerivative (0 : Velocity) t x + convection (0 : Field) x +
      SingularClosure.gradient (0 : Vec → ℝ) x =
        ν • laplacian (0 : Field) x + (0 : Vec) :=
  nativeForcedEquation_zero ν t x

example {ι : Type*} [Fintype ι]
    (K : ι → Set Vec) (u : ι → Velocity) (times : Set ℝ)
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i t x, x ∉ K i → u i t x = 0)
    (hdiv : ∀ i, ∀ t ∈ times, ∀ x : Vec, divergence (u i t) x = 0) :
    ∀ t ∈ times, ∀ x : Vec,
      divergence (fun y => ∑ i, u i t y) x = 0 :=
  finite_sum_native_divergence_free hclosed hdisjoint hzero hdiv

example {ι : Type*} [Fintype ι]
    (K : ι → Set Vec) (u F : ι → Velocity) (p : ι → Pressure)
    (times : Set ℝ) (ν : ℝ)
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (huzero : ∀ i t x, x ∉ K i → u i t x = 0)
    (hpzero : ∀ i t x, x ∉ K i → p i t x = 0)
    (hFzero : ∀ i t x, x ∉ K i → F i t x = 0)
    (hNS : ∀ i, ∀ t ∈ times, ∀ x : Vec,
      timeDerivative (u i) t x + convection (u i t) x +
        SingularClosure.gradient (p i t) x =
          ν • laplacian (u i t) x + F i t x) :
    ∀ t ∈ times, ∀ x : Vec,
      timeDerivative (fun s y => ∑ i, u i s y) t x +
        convection (fun y => ∑ i, u i t y) x +
        SingularClosure.gradient (fun y => ∑ i, p i t y) x =
          ν • laplacian (fun y => ∑ i, u i t y) x + ∑ i, F i t x :=
  finite_sum_native_forcedNSE ν hclosed hdisjoint huzero hpzero hFzero hNS

end MethbokeAddon.FeffermanFamily.AssemblyTypeChecks

-- BEGIN COMPLETE ORDERED TYPE/AXIOM REPORTS

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt"
#check @MethbokeAddon.FeffermanFamily.SpeedUnboundedAt
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt"
#print axioms MethbokeAddon.FeffermanFamily.SpeedUnboundedAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.speedUnboundedAt"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.speedUnboundedAt
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.speedUnboundedAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.speedUnboundedAt"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.speedUnboundedAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.speedUnboundedAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.terminal_pos"
#check @MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.terminal_pos
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.terminal_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.terminal_pos"
#print axioms MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.terminal_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.terminal_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence"
#check @MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence"
#print axioms MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence_in_carrier"
#check @MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence_in_carrier
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence_in_carrier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence_in_carrier"
#print axioms MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence_in_carrier
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_growth_sequence_in_carrier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_localVelocityBlowup"
#check @MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_localVelocityBlowup
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_localVelocityBlowup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_localVelocityBlowup"
#print axioms MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_localVelocityBlowup
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SpeedUnboundedAt.exists_localVelocityBlowup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.spatial_translate"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.spatial_translate
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.spatial_translate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.spatial_translate"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.spatial_translate
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.spatial_translate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.recenter"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.recenter
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.recenter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.recenter"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.recenter
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.recenter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_smul"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_smul
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_smul"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_spatial_scale"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_spatial_scale
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_spatial_scale"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_spatial_scale"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_spatial_scale
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.positive_spatial_scale"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.time_compress_at_one"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.time_compress_at_one
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.time_compress_at_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.time_compress_at_one"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.time_compress_at_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.time_compress_at_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.parabolic_copy"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.parabolic_copy
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.parabolic_copy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.parabolic_copy"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.parabolic_copy
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.parabolic_copy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeSpatialFDeriv_congr"
#check @MethbokeAddon.FeffermanFamily.nativeSpatialFDeriv_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeSpatialFDeriv_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeSpatialFDeriv_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeSpatialFDeriv_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeSpatialFDeriv_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr"
#check @MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeCoordinateDerivative_congr"
#check @MethbokeAddon.FeffermanFamily.nativeCoordinateDerivative_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeCoordinateDerivative_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeCoordinateDerivative_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeCoordinateDerivative_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeCoordinateDerivative_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeDivergence_congr"
#check @MethbokeAddon.FeffermanFamily.nativeDivergence_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeDivergence_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeDivergence_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeDivergence_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeDivergence_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeGradient_congr"
#check @MethbokeAddon.FeffermanFamily.nativeGradient_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeGradient_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeGradient_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeGradient_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeGradient_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeLaplacian_congr"
#check @MethbokeAddon.FeffermanFamily.nativeLaplacian_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeLaplacian_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeLaplacian_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeLaplacian_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeLaplacian_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeConvection_congr"
#check @MethbokeAddon.FeffermanFamily.nativeConvection_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeConvection_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeConvection_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeConvection_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeConvection_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr"
#check @MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr"
#print axioms MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.nativeForcedEquation_zero"
#check @MethbokeAddon.FeffermanFamily.nativeForcedEquation_zero
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.nativeForcedEquation_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.nativeForcedEquation_zero"
#print axioms MethbokeAddon.FeffermanFamily.nativeForcedEquation_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.nativeForcedEquation_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_native_divergence_free"
#check @MethbokeAddon.FeffermanFamily.finite_sum_native_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_native_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_native_divergence_free"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_native_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_native_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_native_forcedNSE"
#check @MethbokeAddon.FeffermanFamily.finite_sum_native_forcedNSE
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_native_forcedNSE"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_native_forcedNSE"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_native_forcedNSE
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_native_forcedNSE"
