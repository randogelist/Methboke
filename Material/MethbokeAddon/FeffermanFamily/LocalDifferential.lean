import SingularClosure.Contracts

/-!
# Locality of the native forced Navier--Stokes operators

The operators here are exactly `SingularClosure.Contracts`, including the
right-hand time derivative `derivWithin` on `Ici 0`. Local agreement in a full
spacetime neighborhood preserves these operators at every time, including zero.
No differentiability premise is needed for locality of the totalized derivatives.

These are operator identities. They neither assert a seed nor identify two
solutions merely from their common force and initial datum.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped BigOperators Topology

namespace MethbokeAddon.FeffermanFamily

noncomputable section

/-- Joint local equality restricts to equality of spatial slice derivatives. -/
theorem nativeSpatialFDeriv_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → Vec → E} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => f z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => g z.1 z.2)) :
    fderiv ℝ (f t) x = fderiv ℝ (g t) x := by
  have hs : f t =ᶠ[𝓝 x] g t :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  exact hs.fderiv_eq

/-- The native one-sided time derivative is local, also at the initial time. -/
theorem nativeTimeDerivative_congr {u v : Velocity} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => v z.1 z.2)) :
    timeDerivative u t x = timeDerivative v t x := by
  have hs : (fun s : ℝ => u s x) =ᶠ[𝓝 t] (fun s => v s x) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  unfold timeDerivative
  exact hs.derivWithin_eq_of_nhds

/-- A native coordinate derivative depends only on the spacetime germ. -/
theorem nativeCoordinateDerivative_congr {u v : Velocity} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => v z.1 z.2)) (i : Fin 3) :
    coordinateDerivative (u t) i x = coordinateDerivative (v t) i x := by
  unfold coordinateDerivative
  rw [nativeSpatialFDeriv_congr h]

/-- The native divergence is local. -/
theorem nativeDivergence_congr {u v : Velocity} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => v z.1 z.2)) :
    divergence (u t) x = divergence (v t) x := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  rw [nativeCoordinateDerivative_congr h i]

/-- The native pressure gradient is local. -/
theorem nativeGradient_congr {p q : Pressure} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => p z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => q z.1 z.2)) :
    SingularClosure.gradient (p t) x = SingularClosure.gradient (q t) x := by
  unfold SingularClosure.gradient
  rw [nativeSpatialFDeriv_congr h]

/-- Iterating spatial differentiation retains locality. -/
theorem nativeLaplacian_congr {u v : Velocity} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => v z.1 z.2)) :
    laplacian (u t) x = laplacian (v t) x := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun z : ℝ × Vec => coordinateDerivative (u z.1) i z.2)
      =ᶠ[𝓝 (t, x)] (fun z => coordinateDerivative (v z.1) i z.2) := by
    filter_upwards [h.eventuallyEq_nhds] with z hz
    exact nativeCoordinateDerivative_congr hz i
  have hd : fderiv ℝ (coordinateDerivative (u t) i) x =
      fderiv ℝ (coordinateDerivative (v t) i) x :=
    nativeSpatialFDeriv_congr hi
  exact congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i)) hd

/-- The nonlinear convection term depends only on the velocity germ. -/
theorem nativeConvection_congr {u v : Velocity} {t : ℝ} {x : Vec}
    (h : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => v z.1 z.2)) :
    convection (u t) x = convection (v t) x := by
  unfold convection
  rw [nativeSpatialFDeriv_congr h]
  exact congrArg (fderiv ℝ (v t) x) h.self_of_nhds

/-- Local equality of the three fields preserves the actual native forced PDE.
The same viscosity and the same native time-boundary convention are retained. -/
theorem nativeForcedEquation_congr (ν : ℝ)
    {u v F G : Velocity} {p q : Pressure} {t : ℝ} {x : Vec}
    (hu : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => v z.1 z.2))
    (hp : (fun z : ℝ × Vec => p z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => q z.1 z.2))
    (hF : (fun z : ℝ × Vec => F z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => G z.1 z.2)) :
    (timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x + F t x) ↔
    (timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
      ν • laplacian (v t) x + G t x) := by
  rw [nativeTimeDerivative_congr hu, nativeConvection_congr hu,
    nativeGradient_congr hp, nativeLaplacian_congr hu, hF.self_of_nhds]

/-- The zero fields satisfy the native forced equation for every real time. -/
theorem nativeForcedEquation_zero (ν t : ℝ) (x : Vec) :
    timeDerivative (0 : Velocity) t x + convection (0 : Field) x +
        SingularClosure.gradient (0 : Vec → ℝ) x =
      ν • laplacian (0 : Field) x + (0 : Vec) := by
  have hDerivative (i : Fin 3) : coordinateDerivative (0 : Field) i = 0 := by
    funext y
    simp [coordinateDerivative]
  have hGradient : SingularClosure.gradient (0 : Vec → ℝ) x = 0 := by
    ext i
    change (fderiv ℝ (0 : Vec → ℝ) x) (unitVector i) = 0
    simp
  simp [timeDerivative, convection, hGradient, laplacian, hDerivative]

end

end MethbokeAddon.FeffermanFamily
