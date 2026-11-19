import MethbokeAddon.EhrenfestObstruction.PhysicalForcing

/-!
Literal transport cross terms and their cutoff-independent L2 bounds.
These estimates use C1 bounds of a given smooth reference field and the
physical finite Parseval identities for the error field.

Prepared source: external cached compiler and axiom audit are still required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff RealInnerProductSpace

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- The literal bilinear transport `(a · ∇) b`. -/
def physicalTransport (a b : Field) : Field :=
  fun x => fderiv ℝ b x (a x)

theorem physicalTransport_continuous (a b : Field)
    (ha : Continuous a) (hb : ContDiff ℝ ∞ b) :
    Continuous (physicalTransport a b) :=
  (hb.continuous_fderiv (by simp)).clm_apply ha

theorem physicalTransport_norm_le (a b : Field) (x : Vec) :
    ‖physicalTransport a b x‖ ≤ ‖fderiv ℝ b x‖ * ‖a x‖ :=
  ContinuousLinearMap.le_opNorm _ _

/-- Exact quadratic expansion of the actual physical convection operator. -/
theorem convection_add_eq_transport
    (w v : Field) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) :
    convection (w + v) =
      convection w + physicalTransport v w + physicalTransport w v + convection v := by
  funext x
  have hwx := hw.differentiable (by norm_num) x
  have hvx := hv.differentiable (by norm_num) x
  change fderiv ℝ (w + v) x (w x + v x) =
    fderiv ℝ w x (w x) + fderiv ℝ w x (v x) +
      fderiv ℝ v x (w x) + fderiv ℝ v x (v x)
  rw [fderiv_add hwx hvx, ContinuousLinearMap.add_apply, map_add, map_add]
  abel

/-- The true truncation residual in the error equation. -/
def physicalReferenceResidual (U v r : Field) : Field :=
  fun x => physicalTransport r U x + physicalTransport v r x

/-- The residual sign follows directly from the literal differential operator. -/
theorem physicalReferenceResidual_eq_convection_sub
    (U v : Field) (hU : ContDiff ℝ ∞ U) (hv : ContDiff ℝ ∞ v) :
    physicalReferenceResidual U v (U - v) = convection U - convection v := by
  funext x
  have hUx := hU.differentiable (by norm_num) x
  have hvx := hv.differentiable (by norm_num) x
  change fderiv ℝ U x (U x - v x) + fderiv ℝ (U - v) x (v x) =
    fderiv ℝ U x (U x) - fderiv ℝ v x (v x)
  rw [fderiv_sub hUx hvx, map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem physicalReferenceResidual_continuous (U v r : Field)
    (hU : ContDiff ℝ ∞ U) (hv : Continuous v) (hr : ContDiff ℝ ∞ r) :
    Continuous (physicalReferenceResidual U v r) :=
  (physicalTransport_continuous r U hr.continuous hU).add
    (physicalTransport_continuous v r hv hr)

theorem norm_add_sq_le_two (a b : Vec) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hs := (sq_le_sq₀ (norm_nonneg (a + b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem physicalReferenceResidual_norm_sq_le
    (M : ℝ) (hM : 0 ≤ M) (U v r : Field) (x : Vec)
    (hDU : ‖fderiv ℝ U x‖ ≤ M) (hv : ‖v x‖ ≤ M) :
    ‖physicalReferenceResidual U v r x‖ ^ 2 ≤
      (2 * M ^ 2) * ‖r x‖ ^ 2 +
        (6 * M ^ 2) * gradientSquareDensity r x := by
  have hru : ‖physicalTransport r U x‖ ≤ M * ‖r x‖ :=
    (physicalTransport_norm_le r U x).trans
      (mul_le_mul_of_nonneg_right hDU (norm_nonneg _))
  have hvr : ‖physicalTransport v r x‖ ≤ ‖fderiv ℝ r x‖ * M :=
    (physicalTransport_norm_le v r x).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hru2 : ‖physicalTransport r U x‖ ^ 2 ≤ M ^ 2 * ‖r x‖ ^ 2 := by
    calc
      _ ≤ (M * ‖r x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hru
      _ = _ := by ring
  have hvr2 : ‖physicalTransport v r x‖ ^ 2 ≤
      M ^ 2 * (3 * gradientSquareDensity r x) := by
    calc
      _ ≤ (‖fderiv ℝ r x‖ * M) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM)).mpr hvr
      _ = M ^ 2 * ‖fderiv ℝ r x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (fderiv_norm_sq_le_three_gradientSquareDensity r x) (sq_nonneg M)
  have h := norm_add_sq_le_two (physicalTransport r U x) (physicalTransport v r x)
  change ‖physicalTransport r U x + physicalTransport v r x‖ ^ 2 ≤ _
  nlinarith

/-- The truncation residual is controlled by the actual physical H1 tail. -/
theorem physicalReferenceResidual_l2_le
    (M : ℝ) (hM : 0 ≤ M) (U v r : Field)
    (hU : ContDiff ℝ ∞ U) (hv : Continuous v) (hr : ContDiff ℝ ∞ r)
    (hDUM : ∀ x ∈ unitCube, ‖fderiv ℝ U x‖ ≤ M)
    (hvM : ∀ x ∈ unitCube, ‖v x‖ ≤ M) :
    (∫ x in unitCube, ‖physicalReferenceResidual U v r x‖ ^ 2) ≤
      (6 * M ^ 2) * ((∫ x in unitCube, ‖r x‖ ^ 2) + physicalDissipation r) := by
  have hR := physicalReferenceResidual_continuous U v r hU hv hr
  have hiR : IntegrableOn (fun x => ‖physicalReferenceResidual U v r x‖ ^ 2)
      unitCube volume :=
    (hR.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hiE : IntegrableOn (fun x => ‖r x‖ ^ 2) unitCube volume :=
    (hr.continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hiD := gradientSquareDensity_integrableOn hr
  have hE : 0 ≤ ∫ x in unitCube, ‖r x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ ∫ x in unitCube,
        (2 * M ^ 2) * ‖r x‖ ^ 2 + (6 * M ^ 2) * gradientSquareDensity r x := by
      apply integral_mono_ae hiR
        ((hiE.const_mul (2 * M ^ 2)).add (hiD.const_mul (6 * M ^ 2)))
      filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
      exact physicalReferenceResidual_norm_sq_le M hM U v r x (hDUM x hx) (hvM x hx)
    _ = (2 * M ^ 2) * (∫ x in unitCube, ‖r x‖ ^ 2) +
        (6 * M ^ 2) * physicalDissipation r := by
      rw [integral_add (hiE.const_mul (2 * M ^ 2)) (hiD.const_mul (6 * M ^ 2)),
        integral_const_mul, integral_const_mul, physicalDissipation]
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg M) hE]

theorem norm_sub_sub_sq_le_three (a b c : Vec) :
    ‖a - b - c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hn : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_sub_le (a - b) c).trans (add_le_add (norm_sub_le a b) (le_refl ‖c‖))
  have hs := (sq_le_sq₀ (norm_nonneg (a - b - c))
    (add_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))
      (norm_nonneg c))).mpr hn
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖c‖)]

/-- Residual plus the two reference/error transport terms. -/
def physicalErrorForcing (v w R : Field) : Field :=
  fun x => R x - physicalTransport v w x - physicalTransport w v x

theorem physicalErrorForcing_continuous (v w R : Field)
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) (hR : Continuous R) :
    Continuous (physicalErrorForcing v w R) :=
  (hR.sub (physicalTransport_continuous v w hv.continuous hw)).sub
    (physicalTransport_continuous w v hw.continuous hv)

/-- A pointwise estimate separating the residual from the reference C1
constant and the actual error gradient and energy densities. -/
theorem physicalErrorForcing_norm_sq_le
    (M : ℝ) (hM : 0 ≤ M) (v w R : Field) (x : Vec)
    (hv : ‖v x‖ ≤ M) (hDv : ‖fderiv ℝ v x‖ ≤ M) :
    ‖physicalErrorForcing v w R x‖ ^ 2 ≤
      3 * ‖R x‖ ^ 2 + (9 * M ^ 2) * gradientSquareDensity w x +
        (3 * M ^ 2) * ‖w x‖ ^ 2 := by
  have hvw : ‖physicalTransport v w x‖ ≤ ‖fderiv ℝ w x‖ * M :=
    (physicalTransport_norm_le v w x).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hwv : ‖physicalTransport w v x‖ ≤ M * ‖w x‖ :=
    (physicalTransport_norm_le w v x).trans
      (mul_le_mul_of_nonneg_right hDv (norm_nonneg _))
  have hvw2 : ‖physicalTransport v w x‖ ^ 2 ≤
      M ^ 2 * (3 * gradientSquareDensity w x) := by
    calc
      _ ≤ (‖fderiv ℝ w x‖ * M) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM)).mpr hvw
      _ = M ^ 2 * ‖fderiv ℝ w x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (fderiv_norm_sq_le_three_gradientSquareDensity w x) (sq_nonneg M)
  have hwv2 : ‖physicalTransport w v x‖ ^ 2 ≤ M ^ 2 * ‖w x‖ ^ 2 := by
    calc
      _ ≤ (M * ‖w x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hwv
      _ = _ := by ring
  have h := norm_sub_sub_sq_le_three (R x)
    (physicalTransport v w x) (physicalTransport w v x)
  change ‖R x - physicalTransport v w x - physicalTransport w v x‖ ^ 2 ≤ _
  nlinarith

/-- Both cross terms are controlled by the finite error's H1 square, with a
constant independent of the cutoff. No derivative of the error is assumed
small in a supremum norm. -/
theorem finite_physicalErrorForcing_l2_le
    (M : ℝ) (hM : 0 ≤ M) (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (v R : Field)
    (hv : ContDiff ℝ ∞ v) (hR : Continuous R)
    (hvM : ∀ x ∈ unitCube, ‖v x‖ ≤ M)
    (hDvM : ∀ x ∈ unitCube, ‖fderiv ℝ v x‖ ≤ M) :
    (∫ x in unitCube, ‖physicalErrorForcing v (finiteSynthesis N c) R x‖ ^ 2) ≤
      3 * (∫ x in unitCube, ‖R x‖ ^ 2) +
        (12 * M ^ 2) * coefficientDissipation N c := by
  have hw := finiteSynthesis_contDiff N c
  have hF := physicalErrorForcing_continuous v (finiteSynthesis N c) R hv hw hR
  have hiF : IntegrableOn
      (fun x => ‖physicalErrorForcing v (finiteSynthesis N c) R x‖ ^ 2)
      unitCube volume :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hiR : IntegrableOn (fun x => ‖R x‖ ^ 2) unitCube volume :=
    (hR.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hiD := gradientSquareDensity_integrableOn hw
  have hiE : IntegrableOn (fun x => ‖finiteSynthesis N c x‖ ^ 2)
      unitCube volume :=
    (hw.continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hE : (∫ x in unitCube, ‖finiteSynthesis N c x‖ ^ 2) =
      coefficientEnergy N c := by
    rw [← physicalEnergy_eq_integral_norm_sq, FINITE_PHYSICAL_ENERGY_PARSEVAL N c hreal]
  have hEP := mul_le_mul_of_nonneg_left
    (coefficientEnergy_le_dissipation N c) (by positivity : 0 ≤ 3 * M ^ 2)
  calc
    _ ≤ ∫ x in unitCube,
        3 * ‖R x‖ ^ 2 + (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x +
          (3 * M ^ 2) * ‖finiteSynthesis N c x‖ ^ 2 := by
      apply integral_mono_ae hiF
        (((hiR.const_mul 3).add (hiD.const_mul (9 * M ^ 2))).add
          (hiE.const_mul (3 * M ^ 2)))
      filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
      exact physicalErrorForcing_norm_sq_le M hM v (finiteSynthesis N c) R x
        (hvM x hx) (hDvM x hx)
    _ = 3 * (∫ x in unitCube, ‖R x‖ ^ 2) +
        (9 * M ^ 2) * coefficientDissipation N c +
          (3 * M ^ 2) * coefficientEnergy N c := by
      have hsum12 :
          (∫ x in unitCube, 3 * ‖R x‖ ^ 2 +
            (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x) =
          (∫ x in unitCube, 3 * ‖R x‖ ^ 2) +
            ∫ x in unitCube, (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x :=
        integral_add
          (f := fun x : Vec => 3 * ‖R x‖ ^ 2)
          (g := fun x : Vec => (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x)
          (hiR.const_mul 3) (hiD.const_mul (9 * M ^ 2))
      have hsum123 :
          (∫ x in unitCube, 3 * ‖R x‖ ^ 2 +
            (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x +
              (3 * M ^ 2) * ‖finiteSynthesis N c x‖ ^ 2) =
          (∫ x in unitCube, 3 * ‖R x‖ ^ 2 +
            (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x) +
            ∫ x in unitCube, (3 * M ^ 2) * ‖finiteSynthesis N c x‖ ^ 2 :=
        integral_add
          (f := fun x : Vec => 3 * ‖R x‖ ^ 2 +
            (9 * M ^ 2) * gradientSquareDensity (finiteSynthesis N c) x)
          (g := fun x : Vec => (3 * M ^ 2) * ‖finiteSynthesis N c x‖ ^ 2)
          ((hiR.const_mul 3).add (hiD.const_mul (9 * M ^ 2)))
          (hiE.const_mul (3 * M ^ 2))
      rw [hsum123, hsum12,
        integral_const_mul, integral_const_mul, integral_const_mul,
        FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal, hE]
    _ ≤ _ := by linarith

/-- The forced error obeys the cubic differential inequality with explicit
reference and residual terms. The universal self-interaction constant is
independent of the cutoff and of the reference field. -/
theorem FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ M : ℝ, 0 ≤ M →
      ∀ N : ℕ, ∀ c : ℝ → FourierCoeff, ∀ v R : Field,
      ContDiff ℝ ∞ v → Continuous R →
      (∀ x ∈ unitCube, ‖v x‖ ≤ M) →
      (∀ x ∈ unitCube, ‖fderiv ℝ v x‖ ≤ M) →
      ∀ s : Set ℝ, ∀ t : ℝ,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c t k i = 0) →
      SpectralReality (c t) → SpectralSolenoidal (c t) →
      (∀ k ∈ cutoffModes N, ∀ i : Fin 3,
        HasDerivWithinAt (fun r => c r k i)
          (galerkinRhs ν N (c t) k i +
            cutoffCoeff N (fun l => coefficientLeray l
              (datumFourierCoeff
                (physicalErrorForcing v (finiteSynthesis N (c t)) R) l)) k i) s t) →
      ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (c r)) d s t ∧
        d ≤ C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
          (24 * M ^ 2 / ν) * coefficientDissipation N (c t) +
            (6 / ν) * (∫ x in unitCube, ‖R x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY
  refine ⟨C, hC, ?_⟩
  intro ν hν M hM N c v R hv hR hvM hDvM s t hsupp hreal hsol heq
  have hF := physicalErrorForcing_continuous v (finiteSynthesis N (c t)) R
    hv (finiteSynthesis_contDiff N (c t)) hR
  obtain ⟨d, hd, hineq⟩ := hbound ν hν N c
    (physicalErrorForcing v (finiteSynthesis N (c t)) R) hF
    s t hsupp hreal hsol heq
  refine ⟨d, hd, ?_⟩
  have hforce := finite_physicalErrorForcing_l2_le M hM N (c t)
    hreal v R hv hR hvM hDvM
  have hscaled := mul_le_mul_of_nonneg_left hforce (by positivity : 0 ≤ 2 / ν)
  calc
    d ≤ d + (ν / 2) * coefficientLaplacianSquare N (c t) :=
      le_add_of_nonneg_right
        (mul_nonneg (by positivity) (coefficientLaplacianSquare_nonneg N (c t)))
    _ ≤ _ := hineq
    _ ≤ C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
        (2 / ν) * (3 * (∫ x in unitCube, ‖R x‖ ^ 2) +
          (12 * M ^ 2) * coefficientDissipation N (c t)) :=
      add_le_add (le_refl _) hscaled
    _ = _ := by ring

end

end MethbokeAddon.EhrenfestObstruction
