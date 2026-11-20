import FDSNR3ResidualSchwartz.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set Filter SingularClosure MethbokeAddon.FDSNR3
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff SchwartzMap Topology
open LineDeriv

example : FamilySpacetime = (ℝ × (ℝ × Vec)) := rfl

example (H : 𝓢(FamilySpacetime, Vec)) (lam t : ℝ) (x : Vec) :
    schwartzFamilyVelocity H lam t x = H (lam, (t, x)) := rfl

example : familySpaceInclusion = familySpatialInclusion.comp spatialSliceCLM := rfl

example (H : 𝓢(FamilySpacetime, Vec)) :
    familySpatialJacobian H = SchwartzMap.postcompCLM
      ((ContinuousLinearMap.compL ℝ Vec FamilySpacetime Vec).flip familySpaceInclusion)
      (SchwartzMap.fderivCLM ℝ FamilySpacetime Vec H) := rfl

example (H : 𝓢(FamilySpacetime, Vec)) (i : Fin 3) :
    familySpaceDerivative H i = ∂_{familySpaceInclusion (unitVector i)} H := rfl

example (H : 𝓢(FamilySpacetime, Vec)) :
    familySpaceLaplacian H =
      ∑ i : Fin 3, familySpaceDerivative (familySpaceDerivative H i) i := rfl

example (H : 𝓢(FamilySpacetime, Vec)) :
    familyTimeDerivative H = ∂_{((0 : ℝ), ((1 : ℝ), (0 : Vec)))} H := rfl

example (B : ℝ × Vec → Vec) (q : FamilySpacetime) : liftedSeed B q = B q.2 := rfl

example (B : ℝ × Vec → Vec) (q : FamilySpacetime) :
    liftedSeedJacobian B q = (fderiv ℝ B q.2).comp spatialSliceCLM := rfl

example (ν : ℝ) (B : ℝ × Vec → Vec) (hB : Function.HasTemperateGrowth B)
    (H : 𝓢(FamilySpacetime, Vec)) :
    jointResidualSchwartz ν B hB H =
      familyTimeDerivative H - ν • familySpaceLaplacian H +
        SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec))
          (liftedSeed_temperate hB) (familySpatialJacobian H) +
        SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec)).flip
          (liftedSeedJacobian_temperate hB) H +
        SchwartzMap.pairing (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec))
          (familySpatialJacobian H) H := rfl


example : ∀ (x : Vec),
    familySpaceInclusion x = (0, (0, x)) :=
  @familySpaceInclusion_apply

example : ∀ (H : 𝓢(FamilySpacetime, Vec))
    (lam t : ℝ) (x : Vec),
    familySpatialJacobian H (lam, (t, x)) =
      fderiv ℝ (schwartzFamilyVelocity H lam t) x :=
  @familySpatialJacobian_apply

example : ∀ (H : 𝓢(FamilySpacetime, Vec))
    (i : Fin 3) (lam t : ℝ) (x : Vec),
    familySpaceDerivative H i (lam, (t, x)) =
      coordinateDerivative (schwartzFamilyVelocity H lam t) i x :=
  @familySpaceDerivative_apply

example : ∀ (H : 𝓢(FamilySpacetime, Vec))
    (lam t : ℝ) (x : Vec),
    familySpaceLaplacian H (lam, (t, x)) =
      laplacian (schwartzFamilyVelocity H lam t) x :=
  @familySpaceLaplacian_apply

example : ∀ (H : 𝓢(FamilySpacetime, Vec))
    (lam t : ℝ) (x : Vec),
    HasDerivAt (fun r : ℝ => schwartzFamilyVelocity H lam r x)
      (familyTimeDerivative H (lam, (t, x))) t :=
  @familyTimeDerivative_hasDerivAt

example : ∀ (H : 𝓢(FamilySpacetime, Vec))
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ Ioi (0 : ℝ))
    (lam t : ℝ) (x : Vec),
    familyTimeDerivative H (lam, (t, x)) =
      timeDerivative (schwartzFamilyVelocity H lam) t x :=
  @familyTimeDerivative_native

example : ∀ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Function.HasTemperateGrowth f),
    Function.HasTemperateGrowth (fderiv ℝ f) :=
  @temperate_fderiv

example : ∀ {B : ℝ × Vec → Vec}
    (hB : Function.HasTemperateGrowth B),
    Function.HasTemperateGrowth (liftedSeed B) :=
  @liftedSeed_temperate

example : ∀ {B : ℝ × Vec → Vec}
    (hB : Function.HasTemperateGrowth B),
    Function.HasTemperateGrowth (liftedSeedJacobian B) :=
  @liftedSeedJacobian_temperate

example : ∀ {B : ℝ × Vec → Vec}
    (hB : Function.HasTemperateGrowth B) (lam t : ℝ) (x : Vec),
    liftedSeedJacobian B (lam, (t, x)) = fderiv ℝ (fun y : Vec => B (t, y)) x :=
  @liftedSeedJacobian_apply

example : ∀ (ν : ℝ) (B : ℝ × Vec → Vec) (hB : Function.HasTemperateGrowth B)
    (H : 𝓢(FamilySpacetime, Vec))
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ Ioi (0 : ℝ))
    (lam t : ℝ) (x : Vec),
    jointResidualSchwartz ν B hB H (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν (fun r y => B (r, y)) 0
        (schwartzFamilyVelocity H lam) t x :=
  @jointResidualSchwartz_eq_native

example : ∀ (ν : ℝ) (u : Velocity) (B : ℝ × Vec → Vec)
    (hB : Function.HasTemperateGrowth B) (H : 𝓢(FamilySpacetime, Vec))
    (S : Set ℝ) (hS : S ⊆ Ioi (0 : ℝ))
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ S)
    (heq : ∀ t ∈ S, ∀ x : Vec, B (t, x) = u t x)
    (lam t : ℝ) (x : Vec),
    jointResidualSchwartz ν B hB H (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x :=
  @jointResidualSchwartz_eq_original

example : ∀ (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ),
    GlobalSchwartzBounds (schwartzFamilyVelocity H lam) :=
  @globalSchwartzBounds_of_jointSchwartz

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.FamilySpacetime"
#check @MethbokeAddon.FDSNR3.FamilySpacetime
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.FamilySpacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.FamilySpacetime"
#print axioms MethbokeAddon.FDSNR3.FamilySpacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.FamilySpacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzFamilyVelocity"
#check @MethbokeAddon.FDSNR3.schwartzFamilyVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzFamilyVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzFamilyVelocity"
#print axioms MethbokeAddon.FDSNR3.schwartzFamilyVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzFamilyVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpaceInclusion"
#check @MethbokeAddon.FDSNR3.familySpaceInclusion
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpaceInclusion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpaceInclusion"
#print axioms MethbokeAddon.FDSNR3.familySpaceInclusion
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpaceInclusion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpaceInclusion_apply"
#check @MethbokeAddon.FDSNR3.familySpaceInclusion_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpaceInclusion_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpaceInclusion_apply"
#print axioms MethbokeAddon.FDSNR3.familySpaceInclusion_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpaceInclusion_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpatialJacobian"
#check @MethbokeAddon.FDSNR3.familySpatialJacobian
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpatialJacobian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpatialJacobian"
#print axioms MethbokeAddon.FDSNR3.familySpatialJacobian
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpatialJacobian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpatialJacobian_apply"
#check @MethbokeAddon.FDSNR3.familySpatialJacobian_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpatialJacobian_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpatialJacobian_apply"
#print axioms MethbokeAddon.FDSNR3.familySpatialJacobian_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpatialJacobian_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpaceDerivative"
#check @MethbokeAddon.FDSNR3.familySpaceDerivative
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpaceDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpaceDerivative"
#print axioms MethbokeAddon.FDSNR3.familySpaceDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpaceDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpaceDerivative_apply"
#check @MethbokeAddon.FDSNR3.familySpaceDerivative_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpaceDerivative_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpaceDerivative_apply"
#print axioms MethbokeAddon.FDSNR3.familySpaceDerivative_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpaceDerivative_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpaceLaplacian"
#check @MethbokeAddon.FDSNR3.familySpaceLaplacian
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpaceLaplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpaceLaplacian"
#print axioms MethbokeAddon.FDSNR3.familySpaceLaplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpaceLaplacian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpaceLaplacian_apply"
#check @MethbokeAddon.FDSNR3.familySpaceLaplacian_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpaceLaplacian_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpaceLaplacian_apply"
#print axioms MethbokeAddon.FDSNR3.familySpaceLaplacian_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpaceLaplacian_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familyTimeDerivative"
#check @MethbokeAddon.FDSNR3.familyTimeDerivative
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familyTimeDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familyTimeDerivative"
#print axioms MethbokeAddon.FDSNR3.familyTimeDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familyTimeDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familyTimeDerivative_hasDerivAt"
#check @MethbokeAddon.FDSNR3.familyTimeDerivative_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familyTimeDerivative_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familyTimeDerivative_hasDerivAt"
#print axioms MethbokeAddon.FDSNR3.familyTimeDerivative_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familyTimeDerivative_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familyTimeDerivative_native"
#check @MethbokeAddon.FDSNR3.familyTimeDerivative_native
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familyTimeDerivative_native"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familyTimeDerivative_native"
#print axioms MethbokeAddon.FDSNR3.familyTimeDerivative_native
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familyTimeDerivative_native"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.temperate_fderiv"
#check @MethbokeAddon.FDSNR3.temperate_fderiv
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.temperate_fderiv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.temperate_fderiv"
#print axioms MethbokeAddon.FDSNR3.temperate_fderiv
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.temperate_fderiv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.liftedSeed"
#check @MethbokeAddon.FDSNR3.liftedSeed
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.liftedSeed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.liftedSeed"
#print axioms MethbokeAddon.FDSNR3.liftedSeed
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.liftedSeed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.liftedSeedJacobian"
#check @MethbokeAddon.FDSNR3.liftedSeedJacobian
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.liftedSeedJacobian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.liftedSeedJacobian"
#print axioms MethbokeAddon.FDSNR3.liftedSeedJacobian
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.liftedSeedJacobian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.liftedSeed_temperate"
#check @MethbokeAddon.FDSNR3.liftedSeed_temperate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.liftedSeed_temperate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.liftedSeed_temperate"
#print axioms MethbokeAddon.FDSNR3.liftedSeed_temperate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.liftedSeed_temperate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.liftedSeedJacobian_temperate"
#check @MethbokeAddon.FDSNR3.liftedSeedJacobian_temperate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.liftedSeedJacobian_temperate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.liftedSeedJacobian_temperate"
#print axioms MethbokeAddon.FDSNR3.liftedSeedJacobian_temperate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.liftedSeedJacobian_temperate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.liftedSeedJacobian_apply"
#check @MethbokeAddon.FDSNR3.liftedSeedJacobian_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.liftedSeedJacobian_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.liftedSeedJacobian_apply"
#print axioms MethbokeAddon.FDSNR3.liftedSeedJacobian_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.liftedSeedJacobian_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointResidualSchwartz"
#check @MethbokeAddon.FDSNR3.jointResidualSchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointResidualSchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointResidualSchwartz"
#print axioms MethbokeAddon.FDSNR3.jointResidualSchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointResidualSchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_native"
#check @MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_native
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_native"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_native"
#print axioms MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_native
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_native"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_original"
#check @MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_original
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_original"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_original"
#print axioms MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_original
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointResidualSchwartz_eq_original"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.globalSchwartzBounds_of_jointSchwartz"
#check @MethbokeAddon.FDSNR3.globalSchwartzBounds_of_jointSchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.globalSchwartzBounds_of_jointSchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.globalSchwartzBounds_of_jointSchwartz"
#print axioms MethbokeAddon.FDSNR3.globalSchwartzBounds_of_jointSchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.globalSchwartzBounds_of_jointSchwartz"

