import MethbokeAddon.WeakFouriermanB.MaximalLerayHopfIdentification
import MethbokeAddon.WeakFouriermanB.FiniteCapOverlap
import QuasiFeffermanB.Cutoff
import QuasiFeffermanB.TailChain

/-!
# A normalized QFB tail and global splice for the same original weak path

The original Leray--Hopf pair is supplied explicitly and retained throughout.
Its identification with every compact maximal-front restriction and its Q09
tail are combined using the same weak representative. Spatial almost-everywhere
agreement becomes pointwise velocity agreement, and the physical equations and
zero pressure means give pressure agreement. One finite interior splice then
produces a global pair preserving the whole original maximal trajectory.

The strict cutoff overlap remains explicit. No replacement weak witness is
chosen by R0, and no tail or global-existence conclusion is assumed in a new
certificate. Prepared source; matching external cached verification and fresh
exact-type/axiom audits are required. No local Lean execution was used.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure QuasiFeffermanB
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- A normalized tail of the same original weak trajectory agrees pointwise
with the maximal classical velocity and pressure on their whole open overlap.
The weak representative is fixed for every compact comparison horizon. -/
theorem maximal_front_tail_overlap_of_same_leray_hopf
    (ν δ : ℝ) (a : Field) (u v w : Velocity) (p q : Pressure)
    (G : WeakGradientTrajectory) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (K : ClassicalTail ν δ w q) (hδ0 : 0 ≤ δ)
    (htail : ∀ t : ℝ, δ ≤ t → v t =ᵐ[volume.restrict unitCube] w t) :
    ∀ t : ℝ, δ < t → ENNReal.ofReal t < Tmax → u t = w t ∧ p t = q t := by
  have hidentify := maximal_front_leray_hopf_identification ν a u v p G Tmax
    hν ha H hv
  intro t hδt htmax
  have ht0 : 0 < t := hδ0.trans_lt hδt
  obtain ⟨T, _, htT, hTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp htmax
  have htTreal : t < T :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0.le).mp htT
  have hT : 0 < T := ht0.trans htTreal
  have hoverlap := finite_cap_tail_overlap_of_same_path_ae ν T δ a u w v p q
    (H.finite_front T hT hTmax) K hδ0
    (by
      intro r hr
      have hr0 : 0 ≤ r := hδ0.trans hr.1.le
      have hrmax : ENNReal.ofReal r < Tmax :=
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0).mpr hr.2).trans hTmax
      exact hidentify r hr0 hrmax)
    (fun r hr => htail r hr.1.le)
  exact ⟨hoverlap.1 t ⟨hδt, htTreal⟩, hoverlap.2 t ⟨hδt, htTreal⟩⟩

/-- Apply Q09 to the supplied original weak witness, derive the actual
velocity/normalized-pressure overlap, and glue one global pair. The returned
tail remains attached to that witness at every tail time; the global pair
preserves the entire maximal front and equals that same tail after the seam.
-/
theorem maximal_front_tail_gluing_of_leray_hopf
    (ν : ℝ) (a : Field) (u v : Velocity) (p : Pressure)
    (G : WeakGradientTrajectory) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hcut : ENNReal.ofReal (cutoff (criticalL2Representative a) ν) < Tmax) :
    ∃ (δ η : ℝ) (w : Velocity) (q : Pressure) (U : Velocity) (P : Pressure),
      cutoff (criticalL2Representative a) ν < δ ∧ δ < η ∧
      ENNReal.ofReal η < Tmax ∧ ClassicalTail ν δ w q ∧
      (∀ t : ℝ, δ ≤ t → v t =ᵐ[volume.restrict unitCube] w t) ∧
      (∀ t : ℝ, δ < t → ENNReal.ofReal t < Tmax → u t = w t ∧ p t = q t) ∧
      GlobalSmoothNSE ν a U P ∧
      (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax → U t = u t ∧ P t = p t) ∧
      ∀ t : ℝ, η ≤ t → U t = w t ∧ P t = q t := by
  have hcut0 : 0 ≤ cutoff (criticalL2Representative a) ν :=
    CUTOFF_NONNEG (criticalL2Representative a) hν
  obtain ⟨T, _, hcutT, hTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp hcut
  have hcutTreal : cutoff (criticalL2Representative a) ν < T :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hcut0).mp hcutT
  have hT : 0 < T := hcut0.trans_lt hcutTreal
  let δ : ℝ := (cutoff (criticalL2Representative a) ν + T) / 2
  let η : ℝ := (δ + T) / 2
  have hcutδ : cutoff (criticalL2Representative a) ν < δ := by
    dsimp [δ]
    linarith
  have hδT : δ < T := by dsimp [δ]; linarith
  have hδ0 : 0 < δ := hcut0.trans_lt hcutδ
  have hδη : δ < η := by dsimp [η]; linarith
  have hηT : η < T := by dsimp [η]; linarith
  have hη0 : 0 ≤ η := hδ0.le.trans hδη.le
  have hηmax : ENNReal.ofReal η < Tmax :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hη0).mpr hηT).trans hTmax
  obtain ⟨w, q, K, htail⟩ :=
    Q09_POST_CUTOFF_SMOOTHNESS hν (smooth_datum_energySigmaZero ha) hv hcutδ
  have hoverlap := maximal_front_tail_overlap_of_same_leray_hopf
    ν δ a u v w p q G Tmax hν ha H hv K hδ0.le htail
  have hrmax (r : ℝ) (hr : r ∈ Ioo δ T) : ENNReal.ofReal r < Tmax :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (hδ0.le.trans hr.1.le)).mpr hr.2).trans hTmax
  obtain ⟨U, P, hglobal, _, hlate⟩ := finite_cap_gluing ν T δ a u w p q
    (H.finite_front T hT hTmax) K hδ0.le hδT
    (fun r hr => (hoverlap r hr.1 (hrmax r hr)).1)
    (fun r hr => (hoverlap r hr.1 (hrmax r hr)).2)
  refine ⟨δ, η, w, q, U, P, hcutδ, hδη, hηmax, K, htail, hoverlap,
    hglobal, ?_, hlate⟩
  intro t ht _
  have hwindow : 0 < t + 1 := by linarith
  have hagree := H.agreement (t + 1) U P hwindow
    (global_smooth_to_initial_front ν (t + 1) a U P hglobal)
    t ⟨ht, by linarith⟩
  exact ⟨hagree.1.symm, hagree.2.symm⟩

end
end MethbokeAddon.WeakFouriermanB
