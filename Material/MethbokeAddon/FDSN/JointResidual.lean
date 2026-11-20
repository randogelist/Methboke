import MethbokeAddon.FDSN.ResidualAdmission

/-!
# Joint smoothness of a family of actual residual forces

The background velocity is smooth only before the terminal time. A common
closed temporal support inside that regular interval allows the full residual
family to be glued to the original force globally, including across time zero
and the terminal time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

theorem family_spatial_fderiv_contDiffAt
    (H : ℝ → Velocity) (q : ℝ × (ℝ × Vec))
    (hH : ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × Vec) => H z.1 z.2.1 z.2.2) q) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × Vec) =>
      fderiv ℝ (H z.1 z.2.1) z.2.2) q := by
  have hmap : ContDiff ℝ ∞ (fun r : (ℝ × (ℝ × Vec)) × Vec =>
      (r.1.1, (r.1.2.1, r.2))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk contDiff_snd)
  have haux : ContDiffAt ℝ ∞
      (fun r : (ℝ × (ℝ × Vec)) × Vec => H r.1.1 r.1.2.1 r.2) (q, q.2.2) :=
    hH.comp (q, q.2.2) hmap.contDiffAt
  exact haux.fderiv contDiffAt_snd.snd (by simp)

theorem family_coordinateDerivative_contDiffOn
    (H : ℝ → Velocity) (T : ℝ)
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      coordinateDerivative (H q.1 q.2.1) j q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} := by
  have hopen : IsOpen {q : ℝ × (ℝ × Vec) | q.2.1 ∈ Ioo (0 : ℝ) T} :=
    isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)
  intro q hq
  exact ((family_spatial_fderiv_contDiffAt H q (hH.contDiffAt (hopen.mem_nhds hq)))
    .clm_apply contDiffAt_const).contDiffWithinAt

theorem family_laplacian_contDiffOn
    (H : ℝ → Velocity) (T : ℝ)
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => laplacian (H q.1 q.2.1) q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} := by
  change ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
    ∑ j : Fin 3, coordinateDerivative (coordinateDerivative (H q.1 q.2.1) j) j q.2.2)
    {q | q.2.1 ∈ Ioo (0 : ℝ) T}
  exact ContDiffOn.sum (fun j _ => family_coordinateDerivative_contDiffOn
    (fun lambda t => coordinateDerivative (H lambda t) j) T
    (family_coordinateDerivative_contDiffOn H T hH j) j)

theorem family_transport_contDiffOn
    (A B : ℝ → Velocity) (T : ℝ)
    (hA : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => A q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T})
    (hB : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => B q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      physicalTransport (A q.1 q.2.1) (B q.1 q.2.1) q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} := by
  have hopen : IsOpen {q : ℝ × (ℝ × Vec) | q.2.1 ∈ Ioo (0 : ℝ) T} :=
    isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)
  intro q hq
  exact ((family_spatial_fderiv_contDiffAt B q (hB.contDiffAt (hopen.mem_nhds hq)))
    .clm_apply (hA.contDiffAt (hopen.mem_nhds hq))).contDiffWithinAt

theorem family_timeDerivative_contDiffOn
    (H : ℝ → Velocity) (T : ℝ)
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => timeDerivative (H q.1) q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} := by
  have hopen : IsOpen {q : ℝ × (ℝ × Vec) | q.2.1 ∈ Ioo (0 : ℝ) T} :=
    isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)
  intro q hq
  have hmap : ContDiff ℝ ∞ (fun r : (ℝ × (ℝ × Vec)) × ℝ =>
      (r.1.1, (r.2, r.1.2.2))) :=
    contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd.snd)
  have haux : ContDiffAt ℝ ∞
      (fun r : (ℝ × (ℝ × Vec)) × ℝ => H r.1.1 r.2 r.1.2.2) (q, q.2.1) :=
    (hH.contDiffAt (hopen.mem_nhds hq)).comp (q, q.2.1) hmap.contDiffAt
  have hd : ContDiffAt ℝ ∞ (fun r : ℝ × (ℝ × Vec) =>
      fderiv ℝ (fun t : ℝ => H r.1 t r.2.2) r.2.1 (1 : ℝ)) q :=
    (haux.fderiv contDiffAt_snd.fst (by simp)).clm_apply contDiffAt_const
  apply ContDiffAt.contDiffWithinAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hq] with r hr
  change derivWithin (fun t : ℝ => H r.1 t r.2.2) (Ici (0 : ℝ)) r.2.1 = _
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hr.1)]
  rfl

theorem residualForce_joint_contDiffOn_front
    (ν : ℝ) (U F : Velocity) (H : ℝ → Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime T))
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      residualForce ν U F (H q.1) q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} := by
  have hU' : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => U q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
    hU.comp contDiffOn_snd (fun _ hq => hq)
  have hF' : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => F q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
    hF.comp contDiffOn_snd (fun _ hq => hq)
  have htime := family_timeDerivative_contDiffOn H T hH
  have hlap := family_laplacian_contDiffOn H T hH
  have hUh := family_transport_contDiffOn (fun _ => U) H T hU' hH
  have hhU := family_transport_contDiffOn H (fun _ => U) T hH hU'
  have hconv := family_transport_contDiffOn H H T hH hH
  exact ((((hF'.add htime).sub (contDiffOn_const.smul hlap)).add hUh).add hhU).add hconv

/-- Common closed support inside the regular time interval yields global joint
parameter-time-space smoothness of the actual residual force. -/
theorem residualForce_joint_contDiff_of_common_timeSupport
    (ν : ℝ) (U F : Velocity) (H : ℝ → Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2))
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T})
    (S : Set ℝ) (hS : IsClosed S) (hST : S ⊆ Ioo (0 : ℝ) T)
    (hsupp : ∀ lambda : ℝ, tsupport (H lambda) ⊆ S) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      residualForce ν U F (H q.1) q.2.1 q.2.2) := by
  have hopen : IsOpen {q : ℝ × (ℝ × Vec) | q.2.1 ∈ Ioo (0 : ℝ) T} :=
    isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)
  have hF' : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) => F q.2.1 q.2.2) :=
    hF.comp contDiff_snd
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2.1 ∈ S
  · exact (residualForce_joint_contDiffOn_front ν U F H T hU hF.contDiffOn hH)
      .contDiffAt (hopen.mem_nhds (hST hq))
  · have hneigh : ∀ᶠ r : ℝ × (ℝ × Vec) in 𝓝 q, r.2.1 ∉ S :=
      (continuous_fst.comp continuous_snd).continuousAt.tendsto.eventually
        (hS.isOpen_compl.mem_nhds hq)
    apply hF'.contDiffAt.congr_of_eventuallyEq
    exact hneigh.mono fun r hr => congrFun
      (residualForce_eq_of_notMem_timeSupport ν U F (H r.1)
        (fun hmem => hr (hsupp r.1 hmem))) r.2.2

theorem residualForce_zero_correction (ν : ℝ) (U F : Velocity) :
    residualForce ν U F 0 = F := by
  funext t x
  exact residualForce_eq_of_zero_germ ν U F 0 t x (Filter.EventuallyEq.rfl)

end MethbokeAddon.FDSN
