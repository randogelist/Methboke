import MethbokeAddon.FDSNR3.Realization
import MethbokeAddon.FDSNR3.SchwartzJets

/-!
# The actual residual as a genuine joint Schwartz correction

A time-localized seed has temperate growth. Its products with the actual
joint Schwartz velocity correction, and every differential term in the
native residual, therefore have genuine Schwartz representatives. The
identification below preserves the native right time derivative at zero.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff SchwartzMap Topology
open LineDeriv

namespace MethbokeAddon.FDSNR3

noncomputable section

abbrev FamilySpacetime := ℝ × (ℝ × Vec)

def schwartzFamilyVelocity (H : 𝓢(FamilySpacetime, Vec)) : ℝ → Velocity :=
  fun lam t x => H (lam, (t, x))

def familySpaceInclusion : Vec →L[ℝ] FamilySpacetime :=
  familySpatialInclusion.comp spatialSliceCLM

@[simp] theorem familySpaceInclusion_apply (x : Vec) :
    familySpaceInclusion x = (0, (0, x)) := rfl

def familySpatialJacobian (H : 𝓢(FamilySpacetime, Vec)) :
    𝓢(FamilySpacetime, Vec →L[ℝ] Vec) :=
  SchwartzMap.postcompCLM
    ((ContinuousLinearMap.compL ℝ Vec FamilySpacetime Vec).flip familySpaceInclusion)
    (SchwartzMap.fderivCLM ℝ FamilySpacetime Vec H)

theorem familySpatialJacobian_apply (H : 𝓢(FamilySpacetime, Vec))
    (lam t : ℝ) (x : Vec) :
    familySpatialJacobian H (lam, (t, x)) =
      fderiv ℝ (schwartzFamilyVelocity H lam t) x := by
  have hmap : HasFDerivAt (fun y : Vec => (lam, (t, y))) familySpaceInclusion x := by
    simpa only [familySpaceInclusion, familySpatialInclusion, spatialSliceCLM,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.id_comp] using
      (hasFDerivAt_const lam x).prodMk
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  exact ((H.hasFDerivAt (lam, (t, x))).comp x hmap).fderiv.symm

def familySpaceDerivative (H : 𝓢(FamilySpacetime, Vec)) (i : Fin 3) :
    𝓢(FamilySpacetime, Vec) := ∂_{familySpaceInclusion (unitVector i)} H

theorem familySpaceDerivative_apply (H : 𝓢(FamilySpacetime, Vec))
    (i : Fin 3) (lam t : ℝ) (x : Vec) :
    familySpaceDerivative H i (lam, (t, x)) =
      coordinateDerivative (schwartzFamilyVelocity H lam t) i x := by
  have h := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i))
    (familySpatialJacobian_apply H lam t x)
  exact h

def familySpaceLaplacian (H : 𝓢(FamilySpacetime, Vec)) :
    𝓢(FamilySpacetime, Vec) :=
  ∑ i : Fin 3, familySpaceDerivative (familySpaceDerivative H i) i

theorem familySpaceLaplacian_apply (H : 𝓢(FamilySpacetime, Vec))
    (lam t : ℝ) (x : Vec) :
    familySpaceLaplacian H (lam, (t, x)) =
      laplacian (schwartzFamilyVelocity H lam t) x := by
  change (∑ i : Fin 3, familySpaceDerivative (familySpaceDerivative H i) i (lam, (t, x))) = _
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [familySpaceDerivative_apply]
  have heq : schwartzFamilyVelocity (familySpaceDerivative H i) lam t =
      coordinateDerivative (schwartzFamilyVelocity H lam t) i := by
    funext y
    exact familySpaceDerivative_apply H i lam t y
  rw [heq]

def familyTimeDerivative (H : 𝓢(FamilySpacetime, Vec)) :
    𝓢(FamilySpacetime, Vec) := ∂_{((0 : ℝ), ((1 : ℝ), (0 : Vec)))} H

theorem familyTimeDerivative_hasDerivAt (H : 𝓢(FamilySpacetime, Vec))
    (lam t : ℝ) (x : Vec) :
    HasDerivAt (fun r : ℝ => schwartzFamilyVelocity H lam r x)
      (familyTimeDerivative H (lam, (t, x))) t := by
  have hmap : HasDerivAt (fun r : ℝ => (lam, (r, x)))
      ((0 : ℝ), ((1 : ℝ), (0 : Vec))) t :=
    (hasDerivAt_const t lam).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact (H.hasFDerivAt (lam, (t, x))).comp_hasDerivAt t hmap

theorem familyTimeDerivative_native (H : 𝓢(FamilySpacetime, Vec))
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ Ioi (0 : ℝ))
    (lam t : ℝ) (x : Vec) :
    familyTimeDerivative H (lam, (t, x)) =
      timeDerivative (schwartzFamilyVelocity H lam) t x := by
  by_cases ht : 0 < t
  · rw [timeDerivative, derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    exact (familyTimeDerivative_hasDerivAt H lam t x).deriv.symm
  · have hnot : t ∉ tsupport (schwartzFamilyVelocity H lam) :=
      fun h => ht (hsupp lam h)
    have hz := MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport
      (schwartzFamilyVelocity H lam) hnot x
    have hzt : (fun r : ℝ => schwartzFamilyVelocity H lam r x) =ᶠ[𝓝 t]
        (fun _ => (0 : Vec)) :=
      hz.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
    have hd : familyTimeDerivative H (lam, (t, x)) = 0 := by
      rw [← (familyTimeDerivative_hasDerivAt H lam t x).deriv]
      simpa using hzt.deriv_eq
    have hnative : timeDerivative (schwartzFamilyVelocity H lam) t x = 0 := by
      calc
        _ = timeDerivative (0 : Velocity) t x :=
          MethbokeAddon.FeffermanFamily.nativeTimeDerivative_congr hz
        _ = 0 := by simp [timeDerivative]
    exact hd.trans hnative.symm

theorem temperate_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Function.HasTemperateGrowth f) :
    Function.HasTemperateGrowth (fderiv ℝ f) := by
  refine ⟨hf.1.fderiv_right (m := ∞) (by simp), ?_⟩
  intro n
  obtain ⟨k, C, hC⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hC x⟩

def liftedSeed (B : ℝ × Vec → Vec) (q : FamilySpacetime) : Vec := B q.2

def liftedSeedJacobian (B : ℝ × Vec → Vec) (q : FamilySpacetime) : Vec →L[ℝ] Vec :=
  (fderiv ℝ B q.2).comp spatialSliceCLM

theorem liftedSeed_temperate {B : ℝ × Vec → Vec}
    (hB : Function.HasTemperateGrowth B) : Function.HasTemperateGrowth (liftedSeed B) :=
  hB.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Vec)).hasTemperateGrowth

theorem liftedSeedJacobian_temperate {B : ℝ × Vec → Vec}
    (hB : Function.HasTemperateGrowth B) :
    Function.HasTemperateGrowth (liftedSeedJacobian B) := by
  have h := ((ContinuousLinearMap.compL ℝ Vec (ℝ × Vec) Vec).flip spatialSliceCLM).hasTemperateGrowth.comp
    (temperate_fderiv hB)
  exact h.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Vec)).hasTemperateGrowth

theorem liftedSeedJacobian_apply {B : ℝ × Vec → Vec}
    (hB : Function.HasTemperateGrowth B) (lam t : ℝ) (x : Vec) :
    liftedSeedJacobian B (lam, (t, x)) = fderiv ℝ (fun y : Vec => B (t, y)) x := by
  have hmap : HasFDerivAt (fun y : Vec => (t, y)) spatialSliceCLM x := by
    simpa only [spatialSliceCLM] using
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact (((hB.1.differentiable (by norm_num)) (t, x)).hasFDerivAt.comp x hmap).fderiv.symm

/-- Every term is a genuine Schwartz operation with a proved multiplier
admission, including both mixed nonlinear terms. -/
def jointResidualSchwartz (ν : ℝ) (B : ℝ × Vec → Vec)
    (hB : Function.HasTemperateGrowth B) (H : 𝓢(FamilySpacetime, Vec)) :
    𝓢(FamilySpacetime, Vec) :=
  familyTimeDerivative H - ν • familySpaceLaplacian H +
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec))
      (liftedSeed_temperate hB) (familySpatialJacobian H) +
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec)).flip
      (liftedSeedJacobian_temperate hB) H +
    SchwartzMap.pairing (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec))
      (familySpatialJacobian H) H

theorem jointResidualSchwartz_eq_native
    (ν : ℝ) (B : ℝ × Vec → Vec) (hB : Function.HasTemperateGrowth B)
    (H : 𝓢(FamilySpacetime, Vec))
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ Ioi (0 : ℝ))
    (lam t : ℝ) (x : Vec) :
    jointResidualSchwartz ν B hB H (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν (fun r y => B (r, y)) 0
        (schwartzFamilyVelocity H lam) t x := by
  change familyTimeDerivative H (lam, (t, x)) -
      ν • familySpaceLaplacian H (lam, (t, x)) +
      familySpatialJacobian H (lam, (t, x)) (B (t, x)) +
      liftedSeedJacobian B (lam, (t, x)) (schwartzFamilyVelocity H lam t x) +
      familySpatialJacobian H (lam, (t, x)) (schwartzFamilyVelocity H lam t x) = _
  rw [familyTimeDerivative_native H hsupp, familySpaceLaplacian_apply,
    familySpatialJacobian_apply, liftedSeedJacobian_apply hB]
  simp only [MethbokeAddon.FDSN.residualForce, Pi.zero_apply, zero_add,
    physicalTransport, convection]

/-- Localization of the seed changes no actual residual where the
correction is supported; elsewhere both residual corrections vanish. -/
theorem jointResidualSchwartz_eq_original
    (ν : ℝ) (u : Velocity) (B : ℝ × Vec → Vec)
    (hB : Function.HasTemperateGrowth B) (H : 𝓢(FamilySpacetime, Vec))
    (S : Set ℝ) (hS : S ⊆ Ioi (0 : ℝ))
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ S)
    (heq : ∀ t ∈ S, ∀ x : Vec, B (t, x) = u t x)
    (lam t : ℝ) (x : Vec) :
    jointResidualSchwartz ν B hB H (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x := by
  rw [jointResidualSchwartz_eq_native ν B hB H (fun l => (hsupp l).trans hS)]
  by_cases ht : t ∈ S
  · have hBt : (fun y : Vec => B (t, y)) = u t := funext (heq t ht)
    simp only [MethbokeAddon.FDSN.residualForce, hBt]
  · have hn : t ∉ tsupport (schwartzFamilyVelocity H lam) := fun h => ht (hsupp lam h)
    rw [MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport ν
      (fun r y => B (r, y)) 0 (schwartzFamilyVelocity H lam) hn,
      MethbokeAddon.FDSN.residualForce_eq_of_notMem_timeSupport ν
        u 0 (schwartzFamilyVelocity H lam) hn]

theorem globalSchwartzBounds_of_jointSchwartz (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    GlobalSchwartzBounds (schwartzFamilyVelocity H lam) := by
  intro N n
  obtain ⟨C, hC, hb⟩ := schwartz_weighted_value_bound (schwartzSliceJet H n) N
  refine ⟨C, hC, ?_⟩
  intro z
  have hw : (1 + ‖z.2‖) ^ N ≤ (1 + ‖z‖) ^ N := by
    gcongr
    exact norm_snd_le z
  change (1 + ‖z.2‖) ^ N *
    ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => H (lam, y)) z‖ ≤ C
  exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
    (by simpa only [schwartzSliceJet_apply] using hb lam z)

end

end MethbokeAddon.FDSNR3
