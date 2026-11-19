import MethbokeAddon.WeakFouriermanB.PhysicalNonlinear
import MethbokeAddon.WeakFouriermanB.InitialFrontAdmission
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
Physical enstrophy evolution on finite classical fronts. The derivative is
derived from the actual spatial-gradient integral and the literal NSE; it is
not an input inequality. Prepared source, requiring external verification.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology RealInnerProductSpace

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

theorem initialFrontSpacetime_uniqueDiffOn (T : ℝ) :
    UniqueDiffOn ℝ (initialFrontSpacetime T) := by
  have heq : initialFrontSpacetime T = Ico (0 : ℝ) T ×ˢ (univ : Set Vec) := by
    ext z
    simp [initialFrontSpacetime]
  rw [heq]
  exact (uniqueDiffOn_Ico 0 T).prod uniqueDiffOn_univ

/-- The within-cylinder derivative gives the ordinary spatial derivative
even at time zero: every spatial slice stays in the cylinder. -/
theorem initial_coordinateDerivative_eq_jointWithin
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Vec) (j : Fin 3) :
    coordinateDerivative (u t) j x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (initialFrontSpacetime T) (t, x) (0, unitVector j) := by
  have hd : DifferentiableWithinAt ℝ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime T) (t, x) :=
    (hu (t, x) ht).differentiableWithinAt (by simp)
  have hc : HasFDerivAt (u t)
      ((fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (initialFrontSpacetime T) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Vec)) x := by
    simpa only [Function.comp_def] using
      hd.hasFDerivWithinAt.comp_hasFDerivAt x (hasFDerivAt_prodMk_right t x)
        (Eventually.of_forall (fun _ => ht))
  rw [coordinateDerivative, hc.fderiv]
  rfl

theorem initial_coordinateDerivative_contDiffOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      (initialFrontSpacetime T) := by
  have hD := hu.fderivWithin (initialFrontSpacetime_uniqueDiffOn T) (m := ∞) (by simp)
  have hA : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fderivWithin ℝ (fun q : ℝ × Vec => u q.1 q.2)
        (initialFrontSpacetime T) z (0, unitVector j)) (initialFrontSpacetime T) :=
    hD.clm_apply contDiffOn_const
  apply hA.congr
  intro z hz
  exact initial_coordinateDerivative_eq_jointWithin u T hu z.1 hz z.2 j

theorem initial_laplacian_contDiffOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => laplacian (u z.1) z.2)
      (initialFrontSpacetime T) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
    ∑ j : Fin 3, coordinateDerivative (coordinateDerivative (u z.1) j) j z.2)
      (initialFrontSpacetime T)
  exact ContDiffOn.sum (fun j _ => initial_coordinateDerivative_contDiffOn
    (fun t => coordinateDerivative (u t) j) T (initial_coordinateDerivative_contDiffOn u T hu j) j)

theorem initial_convection_continuousOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T)) :
    ContinuousOn (fun z : ℝ × Vec => convection (u z.1) z.2) (initialFrontSpacetime T) := by
  have hs : ContinuousOn (fun z : ℝ × Vec =>
      ∑ j : Fin 3, u z.1 z.2 j • coordinateDerivative (u z.1) j z.2)
      (initialFrontSpacetime T) := by
    apply continuousOn_finset_sum
    intro j _
    exact ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      hu.continuousOn).smul (initial_coordinateDerivative_contDiffOn u T hu j).continuousOn
  apply hs.congr
  intro z _
  exact critical_matrix_apply_eq_sum _ _

theorem initial_physicalDissipation_continuousOn_Icc
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun t => physicalDissipation (u t)) (Icc (0 : ℝ) τ) := by
  apply initial_real_cube_integral_continuousOn_Icc T
    (fun t x => gradientSquareDensity (u t) x) _ τ hτT
  simp_rw [gradientSquareDensity_eq_sum_norm_sq]
  apply continuousOn_finset_sum
  intro j _
  exact (initial_coordinateDerivative_contDiffOn u T hu j).continuousOn.norm.pow 2

theorem initial_physicalLaplacianSquare_continuousOn_Icc
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun t => physicalLaplacianSquare (u t)) (Icc (0 : ℝ) τ) :=
  initial_real_cube_integral_continuousOn_Icc T
    (fun t x => ‖laplacian (u t) x‖ ^ 2)
    ((initial_laplacian_contDiffOn u T hu).continuousOn.norm.pow 2) τ hτT

theorem local_coordinateDerivative_contDiffOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      (localFrontSpacetime T) := by
  have hD := hu.fderiv_of_isOpen (localFrontSpacetime_isOpen T) (m := ∞) (by simp)
  have hA : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z (0, unitVector j))
      (localFrontSpacetime T) := hD.clm_apply contDiffOn_const
  apply hA.congr
  intro z hz
  exact local_coordinateDerivative_eq_joint u T hu z.1 hz z.2 j

theorem local_timeDerivative_contDiffOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => timeDerivative u z.1 z.2)
      (localFrontSpacetime T) := by
  have hD := hu.fderiv_of_isOpen (localFrontSpacetime_isOpen T) (m := ∞) (by simp)
  have hA : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z (1, 0))
      (localFrontSpacetime T) := hD.clm_apply contDiffOn_const
  apply hA.congr
  intro z hz
  exact local_timeDerivative_eq_joint u T hu z.1 hz z.2

/-- Schwarz symmetry on the open physical cylinder, applied to the actual
time and coordinate derivative operators. -/
theorem local_time_coordinateDerivative_commute
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (j : Fin 3) (x : Vec) :
    timeDerivative (fun r => coordinateDerivative (u r) j) t x =
      coordinateDerivative (timeDerivative u t) j x := by
  let F : ℝ × Vec → Vec := fun z => u z.1 z.2
  have hz : (t, x) ∈ localFrontSpacetime T := ht
  have hF : ContDiffAt ℝ ∞ F (t, x) :=
    hu.contDiffAt ((localFrontSpacetime_isOpen T).mem_nhds hz)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (t, x) :=
    ((hu.fderiv_of_isOpen (localFrontSpacetime_isOpen T) (m := ∞) (by simp)).contDiffAt
      ((localFrontSpacetime_isOpen T).mem_nhds hz)).differentiableAt (by simp)
  have hs : HasFDerivAt
      (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      ((ContinuousLinearMap.apply ℝ Vec (0, unitVector j)).comp
        (fderiv ℝ (fderiv ℝ F) (t, x))) (t, x) := by
    apply ((ContinuousLinearMap.apply ℝ Vec (0, unitVector j)).hasFDerivAt.comp
      (t, x) hd.hasFDerivAt).congr_of_eventuallyEq
    filter_upwards [(localFrontSpacetime_isOpen T).mem_nhds hz] with z hz'
    exact local_coordinateDerivative_eq_joint u T hu z.1 hz' z.2 j
  have ht' : HasFDerivAt (fun z : ℝ × Vec => timeDerivative u z.1 z.2)
      ((ContinuousLinearMap.apply ℝ Vec (1, 0)).comp
        (fderiv ℝ (fderiv ℝ F) (t, x))) (t, x) := by
    apply ((ContinuousLinearMap.apply ℝ Vec (1, 0)).hasFDerivAt.comp
      (t, x) hd.hasFDerivAt).congr_of_eventuallyEq
    filter_upwards [(localFrontSpacetime_isOpen T).mem_nhds hz] with z hz'
    exact local_timeDerivative_eq_joint u T hu z.1 hz' z.2
  rw [local_timeDerivative_eq_joint _ T (local_coordinateDerivative_contDiffOn u T hu j) t ht x,
    local_coordinateDerivative_eq_joint _ T (local_timeDerivative_contDiffOn u T hu) t ht x j,
    hs.fderiv, ht'.fderiv]
  exact hF.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
      (1, 0) (0, unitVector j)

theorem local_timeDerivative_spatialPeriodic
    (u : Velocity) (T : ℝ)
    (hp : ∀ r ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u r))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : SpatialPeriodic (timeDerivative u t) := by
  intro x j
  have heq : (fun r => u r (x + unitVector j)) =ᶠ[𝓝 t] (fun r => u r x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact hp r hr x j
  exact heq.derivWithin_eq_of_nhds

/-- Differentiating physical enstrophy and integrating by parts transfers
the spatial derivative to the Laplacian of the actual velocity. -/
theorem local_physicalDissipation_hasDerivAt
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (hp : ∀ r ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u r))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => physicalDissipation (u r))
      (-2 * physicalFieldInner (timeDerivative u t) (laplacian (u t))) t := by
  have hj (j : Fin 3) := local_physicalEnergy_hasDerivAt
    (fun r => coordinateDerivative (u r) j) T (local_coordinateDerivative_contDiffOn u T hu j) t ht
  have hsum : HasDerivAt (fun r => ∑ j : Fin 3, physicalEnergy (coordinateDerivative (u r) j))
      (∑ j : Fin 3, 2 * physicalFieldInner (coordinateDerivative (u t) j)
        (timeDerivative (fun r => coordinateDerivative (u r) j) t)) t := by
    simpa only [Fin.sum_univ_three, Pi.add_apply] using! ((hj 0).add (hj 1)).add (hj 2)
  have hD : HasDerivAt (fun r => physicalDissipation (u r))
      (∑ j : Fin 3, 2 * physicalFieldInner (coordinateDerivative (u t) j)
        (timeDerivative (fun r => coordinateDerivative (u r) j) t)) t := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact physicalDissipation_eq_sum_coordinateEnergy (u r) (local_spatial_slice_contDiff u T hu r hr)
  have hfield (j : Fin 3) : timeDerivative (fun r => coordinateDerivative (u r) j) t =
      coordinateDerivative (timeDerivative u t) j :=
    funext (local_time_coordinateDerivative_commute u T hu t ht j)
  simp_rw [hfield] at hD
  have hpair := critical_integral_inner_laplacian (timeDerivative u t) (u t)
    (local_spatial_slice_contDiff _ T (local_timeDerivative_contDiffOn u T hu) t ht)
    (local_spatial_slice_contDiff u T hu t ht)
    (local_timeDerivative_spatialPeriodic u T hp t ht) (hp t ht)
  have hswap : (∑ j : Fin 3, physicalFieldInner (coordinateDerivative (u t) j)
      (coordinateDerivative (timeDerivative u t) j)) =
      -(physicalFieldInner (timeDerivative u t) (laplacian (u t))) := by
    have hc (j : Fin 3) : physicalFieldInner (coordinateDerivative (u t) j)
        (coordinateDerivative (timeDerivative u t) j) =
        physicalFieldInner (coordinateDerivative (timeDerivative u t) j)
          (coordinateDerivative (u t) j) := critical_physicalFieldInner_comm _ _
    simp_rw [hc]
    exact (neg_eq_iff_eq_neg.mp hpair.symm)
  rw [← Finset.mul_sum, hswap] at hD
  convert hD using 1 <;> ring

theorem physical_laplacian_divergence_free
    (v : Field) (hv : SmoothSigmaZero v) (x : Vec) :
    divergence (laplacian v) x = 0 := by
  have hs := laplacian_contDiff v hv.smooth
  have hp := laplacian_spatialPeriodic v hv.periodic
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff (laplacian v))
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s (laplacian v) hs hp)
  have hsol : SpectralSolenoidal (datumFourierCoeff (laplacian v)) := by
    rw [datumFourierCoeff_laplacian v hv.smooth hv.periodic]
    intro k
    have hc := smoothSigmaZero_fourier_solenoidal hv k
    calc
      (∑ j : Fin 3, (k j : ℂ) * laplacianCoefficient (datumFourierCoeff v) k j) =
          -(laplacianFrequency k : ℂ) * (∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff v k j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [laplacianCoefficient]
        ring
      _ = 0 := by rw [hc]; ring
  have h := smoothFourierSynthesis_divergence_free (datumFourierCoeff (laplacian v)) hr hsol x
  rwa [smoothFourierSynthesis_datum_eq (laplacian v) hs hp] at h

def physicalEnstrophyRate (ν : ℝ) (v : Field) : ℝ :=
  (-2 * ν) * physicalLaplacianSquare v +
    2 * physicalFieldInner (convection v) (laplacian v)

theorem initial_physicalEnstrophyRate_continuousOn_Icc
    (ν : ℝ) (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun t => physicalEnstrophyRate ν (u t)) (Icc (0 : ℝ) τ) := by
  have hZ := initial_physicalLaplacianSquare_continuousOn_Icc u T hu τ hτT
  have hN : ContinuousOn
      (fun t => physicalFieldInner (convection (u t)) (laplacian (u t)))
      (Icc (0 : ℝ) τ) :=
    initial_real_cube_integral_continuousOn_Icc T
      (fun t x => inner ℝ (convection (u t) x) (laplacian (u t) x))
      ((initial_convection_continuousOn u T hu).inner
        (initial_laplacian_contDiffOn u T hu).continuousOn) τ hτT
  exact (continuousOn_const.mul hZ).add (continuousOn_const.mul hN)

theorem initial_front_enstrophy_pairing
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    -2 * physicalFieldInner (timeDerivative u t) (laplacian (u t)) =
      physicalEnstrophyRate ν (u t) := by
  have hus := initial_front_smooth_slices ν T a u p H t ⟨ht.1.le, ht.2⟩
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T) :=
    H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  have hps : ContDiff ℝ ∞ (p t) := by
    rw [← contDiffOn_univ]
    exact H.pressure_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨ht.1.le, ht.2⟩)
  have hlap := (laplacian_contDiff (u t) hus.smooth).continuous
  have hud : Continuous (timeDerivative u t) :=
    (local_spatial_slice_contDiff _ T (local_timeDerivative_contDiffOn u T hu) t ht).continuous
  have hconv := convection_continuous hus.smooth
  have hgrad := criticalWeak_gradient_continuous (p t) hps
  have hI₁ := physicalFieldInner_integrable (laplacian (u t)) (timeDerivative u t) hlap hud
  have hI₂ := physicalFieldInner_integrable (laplacian (u t)) (convection (u t)) hlap hconv
  have hI₃ := physicalFieldInner_integrable (laplacian (u t)) (SingularClosure.gradient (p t)) hlap hgrad
  have hI₁₂ : IntegrableOn (fun x =>
      inner ℝ (laplacian (u t) x) (timeDerivative u t x) +
        inner ℝ (laplacian (u t) x) (convection (u t) x)) unitCube volume :=
    hI₁.add hI₂
  have heq : timeDerivative u t + convection (u t) + SingularClosure.gradient (p t) =
      ν • laplacian (u t) := funext (H.equation t ⟨ht.1.le, ht.2⟩)
  have h := congrArg (physicalFieldInner (laplacian (u t))) heq
  simp only [physicalFieldInner, Pi.add_apply, inner_add_right,
    Pi.smul_apply, inner_smul_right] at h
  rw [integral_add hI₁₂ hI₃, integral_add hI₁ hI₂, integral_const_mul,
    critical_smooth_integral_inner_gradient_eq_zero _ (p t)
      (laplacian_contDiff (u t) hus.smooth) hps
      (laplacian_spatialPeriodic (u t) hus.periodic) (H.pressure_periodic t ⟨ht.1.le, ht.2⟩)
      (physical_laplacian_divergence_free (u t) hus)] at h
  simp_rw [real_inner_self_eq_norm_sq] at h
  change physicalFieldInner (laplacian (u t)) (timeDerivative u t) +
    physicalFieldInner (laplacian (u t)) (convection (u t)) + 0 =
      ν * physicalLaplacianSquare (u t) at h
  rw [critical_physicalFieldInner_comm (laplacian (u t)) (timeDerivative u t),
    critical_physicalFieldInner_comm (laplacian (u t)) (convection (u t))] at h
  unfold physicalEnstrophyRate
  linarith

theorem initial_front_physicalEnstrophy_hasDerivAt
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => physicalDissipation (u r)) (physicalEnstrophyRate ν (u t)) t := by
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T) :=
    H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  have h := local_physicalDissipation_hasDerivAt u T hu
    (fun r hr => H.velocity_periodic r ⟨hr.1.le, hr.2⟩) t ht
  rwa [initial_front_enstrophy_pairing ν T a u p H t ht] at h

theorem INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC :
    ∃ C : ℝ, 0 < C ∧ ∀ ν T : ℝ, 0 < ν → ∀ a : Field,
      ∀ u : Velocity, ∀ p : Pressure, InitialClassicalFront ν T a u p →
      ∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivAt (fun r => physicalDissipation (u r)) (physicalEnstrophyRate ν (u t)) t ∧
        physicalEnstrophyRate ν (u t) + ν * physicalLaplacianSquare (u t) ≤
          C / ν ^ 3 * physicalDissipation (u t) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := PHYSICAL_NONLINEAR_ABSORPTION
  refine ⟨C, hC, ?_⟩
  intro ν T hν a u p H t ht
  refine ⟨initial_front_physicalEnstrophy_hasDerivAt ν T a u p H t ht, ?_⟩
  have hs := initial_front_smooth_slices ν T a u p H t ⟨ht.1.le, ht.2⟩
  have h := hb ν hν (u t) hs.smooth hs.periodic hs.mean_zero
  change 2 * physicalFieldInner (convection (u t)) (laplacian (u t)) ≤ _ at h
  unfold physicalEnstrophyRate
  linarith

/-- All continuity premises needed by the scalar budget estimate are derived
from the actual initial front, including the time-zero boundary. -/
theorem initial_front_enstrophy_scalar_continuity
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun t => physicalDissipation (u t)) (Icc (0 : ℝ) τ) ∧
    ContinuousOn (fun t => Real.sqrt (physicalLaplacianSquare (u t))) (Icc (0 : ℝ) τ) ∧
    ContinuousOn (fun t => physicalEnstrophyRate ν (u t)) (Icc (0 : ℝ) τ) := by
  exact ⟨initial_physicalDissipation_continuousOn_Icc u T H.velocity_smooth τ hτT,
    Real.continuous_sqrt.comp_continuousOn
      (initial_physicalLaplacianSquare_continuousOn_Icc u T H.velocity_smooth τ hτT),
    initial_physicalEnstrophyRate_continuousOn_Icc ν u T H.velocity_smooth τ hτT⟩

end
end MethbokeAddon.WeakFouriermanB
