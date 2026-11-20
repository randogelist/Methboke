import MethbokeAddon.FDSNR3.ResidualSchwartz

/-!
# Admission and exact realization of the actual Schwartz family

The correction and its native residual are genuine joint Schwartz maps.
Their compact temporal carrier yields the literal positive-support force
contract. The native equation, initial agreement, local Schwartz bounds,
energy and dissipation histories, and late compact blowup are then derived
from the existing seed and explicit physical identities.

Prepared without local Lean execution. External compilation and explicit
consumer/type/axiom evidence govern acceptance.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff SchwartzMap Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

def correctedVelocity (u : Velocity) (H : 𝓢(FamilySpacetime, Vec)) : ℝ → Velocity :=
  fun lam => u + schwartzFamilyVelocity H lam

def correctedForce (F : Velocity) (J : 𝓢(FamilySpacetime, Vec)) : ℝ → Velocity :=
  fun lam => F + schwartzFamilyVelocity J lam

@[simp] theorem correctedVelocity_sub (u : Velocity)
    (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    correctedVelocity u H lam - u = schwartzFamilyVelocity H lam := by
  change u + schwartzFamilyVelocity H lam - u = schwartzFamilyVelocity H lam
  abel

@[simp] theorem correctedForce_sub (F : Velocity)
    (J : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    correctedForce F J lam - F = schwartzFamilyVelocity J lam := by
  change F + schwartzFamilyVelocity J lam - F = schwartzFamilyVelocity J lam
  abel

theorem correctedVelocity_zero (u : Velocity) (H : 𝓢(FamilySpacetime, Vec))
    (hzero : ∀ z : ℝ × Vec, H (0, z) = 0) : correctedVelocity u H 0 = u := by
  have hH : schwartzFamilyVelocity H 0 = 0 := by
    funext t x
    exact hzero (t, x)
  change u + schwartzFamilyVelocity H 0 = u
  rw [hH, add_zero]

theorem correctedForce_zero (F : Velocity) (J : 𝓢(FamilySpacetime, Vec))
    (hzero : ∀ z : ℝ × Vec, J (0, z) = 0) : correctedForce F J 0 = F := by
  have hJ : schwartzFamilyVelocity J 0 = 0 := by
    funext t x
    exact hzero (t, x)
  change F + schwartzFamilyVelocity J 0 = F
  rw [hJ, add_zero]

theorem schwartzFamilyVelocity_smooth (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => schwartzFamilyVelocity H lam z.1 z.2) :=
  (H.smooth ⊤).comp (contDiff_const.prodMk contDiff_id)

theorem correctedVelocity_joint_correction_smooth (u : Velocity)
    (H : 𝓢(FamilySpacetime, Vec)) :
    ContDiff ℝ ∞ (fun q : FamilySpacetime =>
      (correctedVelocity u H q.1 - u) q.2.1 q.2.2) := by
  simpa only [correctedVelocity_sub, schwartzFamilyVelocity] using H.smooth ⊤

theorem correctedForce_joint_correction_smooth (F : Velocity)
    (J : 𝓢(FamilySpacetime, Vec)) :
    ContDiff ℝ ∞ (fun q : FamilySpacetime =>
      (correctedForce F J q.1 - F) q.2.1 q.2.2) := by
  simpa only [correctedForce_sub, schwartzFamilyVelocity] using J.smooth ⊤

theorem correctedVelocity_eq_of_notMem_timeSupport (u : Velocity)
    (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) {t : ℝ}
    (ht : t ∉ tsupport (schwartzFamilyVelocity H lam)) :
    correctedVelocity u H lam t = u t := by
  change u t + schwartzFamilyVelocity H lam t = u t
  rw [image_eq_zero_of_notMem_tsupport ht, add_zero]

theorem correctedForce_eq_of_notMem_timeSupport (F : Velocity)
    (J : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) {t : ℝ}
    (ht : t ∉ tsupport (schwartzFamilyVelocity J lam)) :
    correctedForce F J lam t = F t := by
  change F t + schwartzFamilyVelocity J lam t = F t
  rw [image_eq_zero_of_notMem_tsupport ht, add_zero]

theorem compactTemporalCorrection_of_jointSchwartz
    {a b : ℝ} (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ)
    {S : Set ℝ} (hS : IsCompact S) (hSab : S ⊆ Ioo a b)
    (hsupp : tsupport (schwartzFamilyVelocity H lam) ⊆ S) :
    CompactTemporalCorrection a b (schwartzFamilyVelocity H lam) := by
  exact ⟨schwartzFamilyVelocity_smooth H lam,
    globalSchwartzBounds_of_jointSchwartz H lam,
    hS.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hSab⟩

/-- The explicit pointwise native residual identity also identifies the
whole time-to-field map, so no support or zero-parameter premise for J is
needed separately. -/
theorem schwartzFamilyVelocity_eq_native_residual
    (ν : ℝ) (u : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (lam : ℝ) :
    schwartzFamilyVelocity J lam =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) := by
  funext t x
  exact hnative lam t x

theorem schwartzResidual_timeSupport_subset
    (ν : ℝ) (u : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (lam : ℝ) :
    tsupport (schwartzFamilyVelocity J lam) ⊆
      tsupport (schwartzFamilyVelocity H lam) := by
  rw [schwartzFamilyVelocity_eq_native_residual ν u H J hnative lam]
  simpa only [sub_zero] using MethbokeAddon.FDSN.tsupport_residualForce_sub_subset
    ν u 0 (schwartzFamilyVelocity H lam)

theorem schwartzResidual_zero_parameter
    (ν : ℝ) (u : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (hzero : ∀ z : ℝ × Vec, H (0, z) = 0) :
    ∀ z : ℝ × Vec, J (0, z) = 0 := by
  have hH : schwartzFamilyVelocity H 0 = 0 := by
    funext t x
    exact hzero (t, x)
  intro z
  rw [hnative 0 z.1 z.2, hH, MethbokeAddon.FDSN.residualForce_zero_correction]

theorem correctedForce_eq_native_residual
    (ν : ℝ) (u F : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (lam : ℝ) :
    correctedForce F J lam =
      MethbokeAddon.FDSN.residualForce ν u F (schwartzFamilyVelocity H lam) := by
  rw [residualForce_eq_add_zero_force]
  exact congrArg (fun h : Velocity => F + h)
    (schwartzFamilyVelocity_eq_native_residual ν u H J hnative lam)

theorem commonTemporalSupport_of_schwartz_residual
    (ν a b ε : ℝ) (u F : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (S : Set ℝ) (hS : IsCompact S) (hSab : S ⊆ Ioo a b)
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ S)
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x) :
    CommonTemporalSupport a b ε u F (correctedVelocity u H) (correctedForce F J) := by
  refine ⟨S, hS, hSab, ?_⟩
  intro lam _
  rw [correctedVelocity_sub, correctedForce_sub]
  exact ⟨hsupp lam, (schwartzResidual_timeSupport_subset ν u H J hnative lam).trans (hsupp lam)⟩

theorem weightedSmoothSmallness_corrected
    (ε : ℝ) (u F : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hH0 : ∀ z : ℝ × Vec, H (0, z) = 0)
    (hJ0 : ∀ z : ℝ × Vec, J (0, z) = 0) :
    WeightedSmoothSmallness ε u F (correctedVelocity u H) (correctedForce F J) := by
  apply weightedSmoothSmallness_of_schwartz_corrections ε u F
    (correctedVelocity u H) (correctedForce F J) H J
  · intro lam z
    simp only [correctedVelocity_sub, schwartzFamilyVelocity]
  · intro lam z
    simp only [correctedForce_sub, schwartzFamilyVelocity]
  · exact hH0
  · exact hJ0

/-- All native realization/admission clauses follow from the actual
Schwartz correction and residual, the physical divergence identity, and
the actual energy/dissipation histories. The side conditions are explicit
and contain no family-existence or realization assertion. -/
theorem exactRealizationAndAgreement_of_schwartz_residual
    {ν T a b ε : ℝ} {u F : Velocity} {p : Pressure}
    (hseed : Seed ν T u p F) (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (H J : 𝓢(FamilySpacetime, Vec))
    (S : Set ℝ) (hS : IsCompact S) (hSab : S ⊆ Ioo a b)
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ S)
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (hdiv : ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      divergence (correctedVelocity u H lam t) x = 0)
    (henergy : ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
      Integrable (fun x : Vec => ‖correctedVelocity u H lam t x‖ ^ 2) volume)
    (hdissipation : ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
      Integrable (gradientSquare (correctedVelocity u H lam t)) volume)
    (hhistory : EnergyDissipationPreservation T ε u (correctedVelocity u H)) :
    ExactRealizationAndAgreement ν T a b ε u p F
      (correctedVelocity u H) (correctedForce F J) := by
  intro lam hlam
  have hH : CompactTemporalCorrection a b (schwartzFamilyVelocity H lam) :=
    compactTemporalCorrection_of_jointSchwartz H lam hS hSab (hsupp lam)
  have hJsupp : tsupport (schwartzFamilyVelocity J lam) ⊆ S :=
    (schwartzResidual_timeSupport_subset ν u H J hnative lam).trans (hsupp lam)
  have hJ : CompactTemporalCorrection a b (schwartzFamilyVelocity J lam) :=
    compactTemporalCorrection_of_jointSchwartz J lam hS hSab hJsupp
  have hHregular : tsupport (schwartzFamilyVelocity H lam) ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans (hH.2.2.2 ht).1, (hH.2.2.2 ht).2.trans hbT⟩
  have hcorrectiondiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      divergence (schwartzFamilyVelocity H lam t) x = 0 := by
    intro t ht x
    have hsum := MethbokeAddon.FDSN.native_divergence_add (u t)
      (schwartzFamilyVelocity H lam t)
      (preterminal_slice_smooth hseed.front.velocity_smooth ht)
      (hH.1.comp (contDiff_const.prodMk contDiff_id)) x
    have hcorrected := hdiv lam hlam t ht x
    change divergence (u t + schwartzFamilyVelocity H lam t) x = 0 at hcorrected
    rw [hsum, hseed.front.divergence_free t ht x, zero_add] at hcorrected
    exact hcorrected
  have hfront : PreterminalNSE ν T (correctedVelocity u H lam) p
      (correctedForce F J lam) := by
    rw [correctedForce_eq_native_residual ν u F H J hnative lam]
    exact hseed.front.add_residual hH.1 hHregular hcorrectiondiv
  have houtside : ∀ t : ℝ, t ∉ Ioo a b →
      correctedVelocity u H lam t = u t ∧ correctedForce F J lam t = F t := by
    intro t ht
    exact ⟨correctedVelocity_eq_of_notMem_timeSupport u H lam
        (fun hm => ht (hH.2.2.2 hm)),
      correctedForce_eq_of_notMem_timeSupport F J lam
        (fun hm => ht (hJ.2.2.2 hm))⟩
  have hinitial : correctedVelocity u H lam 0 = u 0 :=
    (houtside 0 (fun h => (not_lt_of_ge ha.le) h.1)).1
  refine ⟨hfront, hseed.local_schwartz.add_global hH.1 hH.2.1,
    hseed.force.add (hJ.admissibleForce ha hab), hinitial, ?_, ?_, houtside,
    hseed.bounded_energy.of_equal_history (henergy lam hlam)
      (fun t ht => (hhistory lam hlam t ht).1),
    hseed.finite_dissipation.of_equal_history (hdissipation lam hlam)
      (fun t ht => (hhistory lam hlam t ht).2), ?_⟩
  · simpa only [correctedVelocity_sub] using hH
  · simpa only [correctedForce_sub] using hJ
  · apply compactLocalBlowup_of_late_eq hbT hseed.terminal_blowup
    intro t ht
    exact (houtside t (fun h => (not_lt_of_ge ht.1.le) h.2)).1

end

end MethbokeAddon.FDSNR3
