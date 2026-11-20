import MethbokeAddon.FDSN.ResidualLocality
import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution
import MethbokeAddon.FeffermanFamily.FamilyContracts

/-!
# Admissibility of compactly time-localized residual forcing

The seed velocity is required to be smooth only before T. Global smoothness
of the new force is obtained by locality outside the correction's closed
temporal support, not by extending the seed smoothly through T.
-/

set_option autoImplicit false

noncomputable section

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.WeakFouriermanB
open MethbokeAddon.FeffermanFamily
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

theorem residual_local_laplacian_contDiffOn
    (h : Velocity) (T : ℝ)
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => laplacian (h z.1) z.2)
      (localFrontSpacetime T) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
    ∑ j : Fin 3, coordinateDerivative (coordinateDerivative (h z.1) j) j z.2)
    (localFrontSpacetime T)
  exact ContDiffOn.sum (fun j _ => local_coordinateDerivative_contDiffOn
    (fun t => coordinateDerivative (h t) j) T (local_coordinateDerivative_contDiffOn h T hh j) j)

theorem residual_local_transport_contDiffOn
    (a b : Velocity) (T : ℝ)
    (ha : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => a z.1 z.2) (localFrontSpacetime T))
    (hb : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => b z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => physicalTransport (a z.1) (b z.1) z.2)
      (localFrontSpacetime T) := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      ∑ j : Fin 3, a z.1 z.2 j • coordinateDerivative (b z.1) j z.2)
      (localFrontSpacetime T) := by
    apply ContDiffOn.sum
    intro j _
    exact ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn ha).smul
      (local_coordinateDerivative_contDiffOn b T hb j)
  apply hs.congr
  intro z _
  exact critical_matrix_apply_eq_sum _ _

set_option maxHeartbeats 800000 in
theorem residualForce_contDiffOn_front
    (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime T))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => residualForce ν U F h z.1 z.2)
      (localFrontSpacetime T) := by
  have htime : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => timeDerivative h z.1 z.2)
      (localFrontSpacetime T) := local_timeDerivative_contDiffOn h T hh
  have hlap : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => laplacian (h z.1) z.2)
      (localFrontSpacetime T) := residual_local_laplacian_contDiffOn h T hh
  have hviscous : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => ν • laplacian (h z.1) z.2)
      (localFrontSpacetime T) :=
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × Vec => ν)
      (localFrontSpacetime T)).smul hlap
  have hUh : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => physicalTransport (U z.1) (h z.1) z.2)
      (localFrontSpacetime T) := residual_local_transport_contDiffOn U h T hU hh
  have hhU : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => physicalTransport (h z.1) (U z.1) z.2)
      (localFrontSpacetime T) := residual_local_transport_contDiffOn h U T hh hU
  have hconv : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => convection (h z.1) z.2)
      (localFrontSpacetime T) := residual_local_transport_contDiffOn h h T hh hh
  have hlinear : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      F z.1 z.2 + timeDerivative h z.1 z.2 - ν • laplacian (h z.1) z.2)
      (localFrontSpacetime T) := (hF.add htime).sub hviscous
  have hfirst : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      F z.1 z.2 + timeDerivative h z.1 z.2 - ν • laplacian (h z.1) z.2 +
        physicalTransport (U z.1) (h z.1) z.2)
      (localFrontSpacetime T) := hlinear.add hUh
  have hsecond : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      F z.1 z.2 + timeDerivative h z.1 z.2 - ν • laplacian (h z.1) z.2 +
        physicalTransport (U z.1) (h z.1) z.2 + physicalTransport (h z.1) (U z.1) z.2)
      (localFrontSpacetime T) := hfirst.add hhU
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
    F z.1 z.2 + timeDerivative h z.1 z.2 - ν • laplacian (h z.1) z.2 +
      physicalTransport (U z.1) (h z.1) z.2 + physicalTransport (h z.1) (U z.1) z.2 +
      convection (h z.1) z.2) (localFrontSpacetime T)
  exact hsecond.add hconv

/-- Global smoothness of the actual new forcing follows from preterminal
seed regularity and support strictly inside the regular time domain. -/
theorem residualForce_contDiff_of_timeSupport_inside
    (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T))
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => residualForce ν U F h z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.1 ∈ tsupport h
  · exact (residualForce_contDiffOn_front ν U F h T hU hF.contDiffOn hh).contDiffAt
      ((localFrontSpacetime_isOpen T).mem_nhds (hsupp hz))
  · have hneigh : ∀ᶠ q : ℝ × Vec in 𝓝 z, q.1 ∉ tsupport h :=
      (continuousAt_fst : ContinuousAt (fun q : ℝ × Vec => q.1) z).tendsto.eventually
        ((isClosed_tsupport h).isOpen_compl.mem_nhds hz)
    apply hF.contDiffAt.congr_of_eventuallyEq
    exact hneigh.mono fun q hq =>
      congrFun (residualForce_eq_of_notMem_timeSupport ν U F h hq) q.2

theorem residual_transport_spatialPeriodic
    (a b : Field) (ha : SpatialPeriodic a) (hb : SpatialPeriodic b) :
    SpatialPeriodic (physicalTransport a b) := by
  intro x i
  have heq : (fun y : Vec => b (y + unitVector i)) = b :=
    funext (fun y => hb y i)
  have hd : fderiv ℝ b (x + unitVector i) = fderiv ℝ b x := by
    have h := congrArg (fun f : Field => fderiv ℝ f x) heq
    simpa only [fderiv_comp_add_right] using h
  change fderiv ℝ b (x + unitVector i) (a (x + unitVector i)) =
    fderiv ℝ b x (a x)
  rw [hd, ha x i]

theorem residualForce_spatialPeriodic_of_timeSupport_inside
    (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (U t))
    (hF : ∀ t : ℝ, SpatialPeriodic (F t))
    (hh : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (h t))
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ∀ t : ℝ, SpatialPeriodic (residualForce ν U F h t) := by
  intro t
  by_cases ht : t ∈ tsupport h
  · have htT := hsupp ht
    have htime := local_timeDerivative_spatialPeriodic h T hh t htT
    have hlap := laplacian_spatialPeriodic (h t) (hh t htT)
    have hUh := residual_transport_spatialPeriodic (U t) (h t) (hU t htT) (hh t htT)
    have hhU := residual_transport_spatialPeriodic (h t) (U t) (hh t htT) (hU t htT)
    have hconv : SpatialPeriodic (convection (h t)) :=
      residual_transport_spatialPeriodic (h t) (h t) (hh t htT) (hh t htT)
    intro x i
    simp only [residualForce]
    rw [hF t x i, htime x i, hlap x i, hUh x i, hhU x i, hconv x i]
  · rw [residualForce_eq_of_notMem_timeSupport ν U F h ht]
    exact hF t

/-- A compact closed support contained in positive preterminal times has an
explicitly admitted positive compact containing interval. -/
theorem compact_timeSupport_positive_interval
    (h : Velocity) (T : ℝ) (hh : HasCompactSupport h)
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport h ⊆ Icc a b := by
  rcases (tsupport h).eq_empty_or_nonempty with hempty | hnonempty
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    rw [hempty]
    exact empty_subset _
  · obtain ⟨a, ha, hmin⟩ :=
      hh.isCompact.exists_isMinOn hnonempty (continuous_id.continuousOn : ContinuousOn
        (fun t : ℝ => t) (tsupport h))
    have ha0 : 0 < a := (hsupp ha).1
    have haT : a < T := (hsupp ha).2
    refine ⟨a / 2, T + 1, by linarith, by linarith, ?_⟩
    intro t ht
    have hat : a ≤ t := hmin ht
    have htT : t < T := (hsupp ht).2
    constructor <;> linarith

/-- Full force admission, using the actual native smoothness, periodicity
and compact-positive-time-support contract. -/
theorem admissiblePeriodicForce_residual
    (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hF : AdmissiblePeriodicForce F)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T))
    (hUp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (U t))
    (hhp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (h t))
    (hhcompact : HasCompactSupport h)
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    AdmissiblePeriodicForce (residualForce ν U F h) := by
  exact {
    smooth := residualForce_contDiff_of_timeSupport_inside ν U F h T hU hF.smooth hh hsupp
    periodic := residualForce_spatialPeriodic_of_timeSupport_inside ν U F h T hUp
      hF.periodic hhp hsupp
    time_support := residualForce_positive_time_support ν U F h hF.time_support
      (compact_timeSupport_positive_interval h T hhcompact hsupp)
  }

end MethbokeAddon.FDSN

