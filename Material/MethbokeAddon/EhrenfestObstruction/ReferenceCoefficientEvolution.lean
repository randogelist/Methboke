import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution
import SingularClosure.InitialFourier

/-!
Time differentiation of the literal physical Fourier integrals on an actual
initial classical front. Interior differentiation and closed-slab continuity
are proved separately so that no boundary differentiation certificate is used.
Source-prepared only; external cached verification is still required.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Metric SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

private theorem reference_mem_of_half_ball {S t r : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) S)
    (hr : r ∈ closedBall t (min t (S - t) / 2)) :
    r ∈ Ioo (0 : ℝ) S := by
  have hh : |r - t| ≤ min t (S - t) / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
  have hleft := min_le_left t (S - t)
  have hright := min_le_right t (S - t)
  have hl := (abs_le.mp hh).1
  have hu := (abs_le.mp hh).2
  constructor <;> linarith [ht.1, ht.2]

/-- Complex-valued version of the actual finite-front cube differentiation lemma. -/
theorem local_hasDerivAt_complex_cube_integral
    (S : ℝ) (F D : ℝ → Vec → ℂ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime S))
    (hD : ContinuousOn (fun z : ℝ × Vec => D z.1 z.2) (localFrontSpacetime S))
    (hd : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Vec,
      HasDerivAt (fun r => F r x) (D t x) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => ∫ x in unitCube, F r x)
      (∫ x in unitCube, D t x) t := by
  let ρ : ℝ := min t (S - t) / 2
  have hρ : 0 < ρ := div_pos (lt_min ht.1 (sub_pos.mpr ht.2)) (by norm_num)
  have hFc (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) S) : Continuous (F r) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hDc (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) S) : Continuous (D r) :=
    hD.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hsubset : closedBall t ρ ×ˢ unitCube ⊆ localFrontSpacetime S := by
    intro z hz
    exact reference_mem_of_half_ball ht hz.1
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall t ρ).prod isCompact_unitCube).exists_bound_of_continuousOn
      (hD.mono hsubset)
  have hbound : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ r ∈ closedBall t ρ, ‖D r x‖ ≤ C := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    intro r hr
    exact hC (r, x) ⟨hr, hx⟩
  have hdiff : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ r ∈ closedBall t ρ, HasDerivAt (fun q => F q x) (D r x) r :=
    Filter.Eventually.of_forall fun x r hr => hd r (reference_mem_of_half_ball ht hr) x
  have hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) (volume.restrict unitCube) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hFc r hr).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict unitCube) (F := F) (F' := D)
    (bound := fun _ : Vec => C) (closedBall_mem_nhds t hρ) hmeas
    ((hFc t ht).continuousOn.integrableOn_compact isCompact_unitCube)
    (hDc t ht).aestronglyMeasurable hbound
    (continuous_const.continuousOn.integrableOn_compact isCompact_unitCube) hdiff).2

/-- Dominated complex integration also preserves continuity at time zero. -/
theorem initial_complex_cube_integral_continuousOn_Icc
    (S : ℝ) (F : ℝ → Vec → ℂ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (initialFrontSpacetime S))
    (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun r => ∫ x in unitCube, F r x) (Icc (0 : ℝ) T) := by
  have hsubset : Icc (0 : ℝ) T ×ˢ unitCube ⊆ initialFrontSpacetime S := by
    intro z hz
    exact ⟨hz.1.1, hz.1.2.trans_lt hTS⟩
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod isCompact_unitCube).exists_bound_of_continuousOn
      (hF.mono hsubset)
  apply continuousOn_of_dominated (μ := volume.restrict unitCube)
    (bound := fun _ : Vec => C)
  · intro r hr
    have hc : Continuous (F r) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hr.1, hr.2.trans_lt hTS⟩)
    exact hc.aestronglyMeasurable
  · intro r hr
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact hC (r, x) ⟨hr, hx⟩
  · exact continuous_const.continuousOn.integrableOn_compact isCompact_unitCube
  · filter_upwards with x
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr.1, hr.2.trans_lt hTS⟩)

/-- A fixed Fourier character preserves joint continuity of the actual integrand. -/
theorem datumFourierIntegrand_continuousOn_spacetime
    (u : Velocity) (s : Set (ℝ × Vec))
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) s)
    (k : Frequency) (i : Fin 3) :
    ContinuousOn (fun z : ℝ × Vec => datumFourierIntegrand (u z.1) k i z.2) s := by
  exact (((fourierCharacter_contDiff k).continuous.star.comp continuous_snd).continuousOn).mul
    (Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn hu))

/-- The time derivative passes through each literal physical Fourier integral. -/
theorem local_datumFourierCoeff_hasDerivAt
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime S))
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) t := by
  apply local_hasDerivAt_complex_cube_integral S
    (fun r x => datumFourierIntegrand (u r) k i x)
    (fun r x => datumFourierIntegrand (timeDerivative u r) k i x)
  · exact datumFourierIntegrand_continuousOn_spacetime u _ hu.continuousOn k i
  · exact datumFourierIntegrand_continuousOn_spacetime (timeDerivative u) _
      (local_timeDerivative_continuousOn u S hu) k i
  · intro r hr x
    have hc := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r
      (local_time_hasDerivAt u S hu r hr x)
    have hz := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hc
    exact hz.const_mul (star (fourierCharacter k x))
  · exact ht

/-- An admitted initial classical front supplies the interior coefficient derivative. -/
theorem initial_front_datumFourierCoeff_hasDerivAt
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) t :=
  local_datumFourierCoeff_hasDerivAt u S
    (H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)) k i t ht

/-- The actual reference coefficient curve is continuous on each shorter closed slab. -/
theorem initial_front_datumFourierCoeff_continuousOn_Icc
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => datumFourierCoeff (u t) k i) (Icc (0 : ℝ) T) :=
  initial_complex_cube_integral_continuousOn_Icc S
    (fun t x => datumFourierIntegrand (u t) k i x)
    (datumFourierIntegrand_continuousOn_spacetime u _ H.velocity_smooth.continuousOn k i)
    T hTS

/-- Differentiating the actual Fourier divergence constraint proves tangency
of the physical time derivative; it is not an independent spectral premise. -/
theorem initial_front_timeDerivative_fourier_solenoidal
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    SpectralSolenoidal (datumFourierCoeff (timeDerivative u t)) := by
  intro k
  have hj (j : Fin 3) :=
    (initial_front_datumFourierCoeff_hasDerivAt ν S a u p H k j t ht).const_mul (k j : ℂ)
  have hsum : HasDerivAt
      (fun r => ∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff (u r) k j)
      (∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff (timeDerivative u t) k j) t := by
    simpa only [Fin.sum_univ_three, Pi.add_apply] using! ((hj 0).add (hj 1)).add (hj 2)
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℂ))
      (∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff (timeDerivative u t) k j) t := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (smoothSigmaZero_fourier_solenoidal
      (initial_front_smooth_slices ν S a u p H r ⟨hr.1.le, hr.2⟩) k).symm
  exact hzero.unique (hasDerivAt_const t (0 : ℂ))

/-- Leray fixes the actual Fourier transform of the physical time derivative. -/
theorem initial_front_timeDerivative_fourier_leray
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) (k : Frequency) :
    coefficientLeray k (datumFourierCoeff (timeDerivative u t) k) =
      datumFourierCoeff (timeDerivative u t) k :=
  coefficientLeray_eq_of_solenoidal k _
    (initial_front_timeDerivative_fourier_solenoidal ν S a u p H t ht k)

end
end MethbokeAddon.EhrenfestObstruction
