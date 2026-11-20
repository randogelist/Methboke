import MethbokeAddon.WeakFouriermanB.LocalGalerkinCompactness
import MethbokeAddon.WeakFouriermanB.LocalSobolevCalculus
import SingularClosure.CriticalPositiveLimit
import SingularClosure.SobolevLimitInitial

/-!
Construction of an actual finite-window Sobolev NSE flow from the Galerkin
approximations. Higher membership and continuity follow from proved uniform
bounds, the untruncated modal equation follows from the actual H0 limit, and
its Sobolev derivative is proved by integration. The canonical construction
also identifies the literal initial Fourier coefficients of the smooth datum.
Prepared source only; matching external cached verification is required.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped Topology Interval

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Finite-window construction from an actual Galerkin limit and explicit
all-order bounds. No physical solution or derivative equation is assumed. -/
theorem local_sobolev_flow_of_galerkin_limit
    (ν : ℝ) (a : Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν a (φ n + 1))
    (T : ℝ) (hT : 0 < T)
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (hbound : ∀ s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T → ‖(g n).sobolevState s t‖ ≤ B) :
    ∃ L : LocalSobolevFlow ν T, ∀ t ∈ Icc (0 : ℝ) T, L.state 0 t = u t := by
  classical
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hcoeff (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
      (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => ((g n).sobolevState s t).val k i) atTop (𝓝 ((u t).val k i)) := by
    have h := ((torusSobolevH0Coeff_continuous k i).tendsto (u t)).comp
      (hconv.tendsto_at ht)
    have heq : (fun n => ((g n).sobolevState s t).val k i) =
        (fun n => ((g n).sobolevState 0 t).val k i) := by
      funext n
      rw [(g n).sobolevState_coeff s ht.1, (g n).sobolevState_coeff 0 ht.1]
    rw [heq]
    exact h
  have hmem (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Memℓp (sobolevWeightedCoeff s (u t).val) 2 := by
    obtain ⟨B, _, hb⟩ := hbound s
    exact (torusSobolev_limit_mem_and_norm_le s
      (fun n => (g n).sobolevState s t) (u t).val B
      (fun n => hb n t ht) (hcoeff s t ht)).choose
  let U : ∀ s : ℕ, ℝ → TorusSobolev s := fun s t =>
    if ht : t ∈ Icc (0 : ℝ) T then ⟨(u t).val, hmem s t ht⟩ else 0
  have hUc (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (U s t).val = (u t).val := by
    have heq : U s t = (⟨(u t).val, hmem s t ht⟩ : TorusSobolev s) := dif_pos ht
    exact congrArg (fun z : TorusSobolev s => z.val) heq
  have hU0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : U 0 t = u t :=
    Subtype.ext (hUc 0 t ht)
  have hUb (s : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖U s t‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := hbound s
    refine ⟨B, hB, ?_⟩
    intro t ht
    obtain ⟨hc, hn⟩ := torusSobolev_limit_mem_and_norm_le s
      (fun n => (g n).sobolevState s t) (u t).val B
      (fun n => hb n t ht) (hcoeff s t ht)
    have heq : U s t = (⟨(u t).val, hc⟩ : TorusSobolev s) := Subtype.ext (hUc s t ht)
    rw [heq]
    exact hn
  have hinc (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      torusSobolevInclusion s (U (s + 1) t) = U s t := by
    apply Subtype.ext
    rw [torusSobolevInclusion_coeff, hUc (s + 1) t ht, hUc s t ht]
  have hU (s : ℕ) : ContinuousOn (U s) (Icc (0 : ℝ) T) := by
    obtain ⟨B, _, hb⟩ := hUb (s + 1)
    have hc (k : Frequency) (i : Fin 3) :
        ContinuousOn (fun t => (U (s + 1) t).val k i) (Icc (0 : ℝ) T) := by
      apply ((torusSobolevH0Coeff_continuous k i).comp_continuousOn hu).congr
      intro t ht
      exact congrArg (fun c : FourierCoeff => c k i) (hUc (s + 1) t ht)
    apply (torusSobolevInclusion_continuousOn_of_coeff_continuousOn
      s (U (s + 1)) (Icc (0 : ℝ) T) B hb hc).congr
    intro t ht
    exact (hinc s t ht).symm
  have hR (s : ℕ) : ContinuousOn
      (fun t => fourierSobolevRhs ν s (U (s + 2) t)) (Icc (0 : ℝ) T) :=
    (fourierSobolevRhs_contDiff ν s).continuous.comp_continuousOn (hU (s + 2))
  have hRc (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (fourierSobolevRhs ν s (U (s + 2) t)).val = fullFourierRhs ν (u t) := by
    have hlower : torusSobolevLower 0 (s + 2) (Nat.zero_le _) (U (s + 2) t) = u t := by
      apply Subtype.ext
      rw [torusSobolevLower_coeff]
      exact hUc (s + 2) t ht
    rw [fourierSobolevRhs_coefficient_eq_fullRhs, hlower]
  have heq := galerkinLimit_coefficient_integral ν a φ hφ g T hT.le u hu hconv
  have hmodal (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
      (k : Frequency) (i : Fin 3) :
      (U s t).val k i = (U s 0).val k i +
        ∫ z in (0 : ℝ)..t, (fourierSobolevRhs ν s (U (s + 2) z)).val k i := by
    rw [hUc s t ht, hUc s 0 hzero, heq t ht k i]
    congr 1
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hz
    exact congrArg (fun c : FourierCoeff => c k i) (hRc s z ⟨hz'.1, hz'.2.trans ht.2⟩).symm
  have hd (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt (U s) (fourierSobolevRhs ν s (U (s + 2) t)) (Icc (0 : ℝ) T) t :=
    local_sobolev_hasDerivWithinAt_of_coefficient_integral s T hT.le (U s)
      (fun z => fourierSobolevRhs ν s (U (s + 2) z)) (hR s) (hmodal s) t ht
  have hlim (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => (g n).sobolevState 0 t) atTop (𝓝 (u t)) := hconv.tendsto_at ht
  have hreal (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : SpectralReality (U 0 t).val := by
    rw [hUc 0 t ht]
    exact torusSobolevH0_reality_of_tendsto (hlim t ht)
      (Filter.Eventually.of_forall (fun n => (g n).sobolevState_reality 0 t ht.1))
  have hsol (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : SpectralSolenoidal (U 0 t).val := by
    rw [hUc 0 t ht]
    exact torusSobolevH0_solenoidal_of_tendsto (hlim t ht)
      (Filter.Eventually.of_forall (fun n => (g n).sobolevState_solenoidal 0 t ht.1))
  have hzeroMode (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : SpectralMeanZero (U 0 t).val := by
    rw [hUc 0 t ht]
    exact torusSobolevH0_zero_mode_of_tendsto (hlim t ht)
      (Filter.Eventually.of_forall (fun n => (g n).sobolevState_zero_mode 0 t ht.1))
  refine ⟨{
    state := U
    continuous := hU
    coeff := fun s t ht => (hUc s t ht).trans (hUc 0 t ht).symm
    derivative := hd
    reality := hreal
    solenoidal := hsol
    mean_zero := hzeroMode
  }, hU0⟩

/-- The local H2 bound constructs the actual finite-window Sobolev flow with
its original smooth datum. The higher norms do not reduce the interval. -/
theorem local_sobolev_flow_of_uniform_H2
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S) :
    ∃ L : LocalSobolevFlow ν T, (L.state 0 0).val = datumFourierCoeff a := by
  classical
  obtain ⟨v, φ, hφ, hv⟩ :=
    local_canonical_galerkin_H0_uniform_subsequence ν hν a ha T hT S hS hH2
  let g := fun n => canonicalGalerkinSolution ν hν a ha (φ n + 1)
  let u : ℝ → TorusSobolev 0 := fun t =>
    if ht : t ∈ Icc (0 : ℝ) T then v ⟨t, ht⟩ else 0
  have hrestrict : (fun t : Icc (0 : ℝ) T => u t.val) = v := by
    funext t
    simp only [u, dif_pos t.property]
  have hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T) := by
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    change TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) => (g n).sobolevState 0 t.val)
      (fun t : Icc (0 : ℝ) T => u t.val) atTop
    rw [hrestrict]
    exact hv
  have hu : ContinuousOn u (Icc (0 : ℝ) T) :=
    hconv.continuousOn (Filter.Eventually.of_forall
      (fun n => ((g n).sobolevState_continuousOn 0).mono (fun t ht => ht.1))).frequently
  have hbound (s : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T → ‖(g n).sobolevState s t‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := local_galerkin_high_order_pointwise ν hν a ha T hT S hS hH2 s
    refine ⟨B + 1, by linarith, ?_⟩
    intro n t ht
    have hn := hb (φ n + 1) (by omega) (g n) t ht
    nlinarith [sq_nonneg (‖(g n).sobolevState s t‖ - 1)]
  obtain ⟨L, hL⟩ := local_sobolev_flow_of_galerkin_limit ν a φ hφ g T hT u hu hconv hbound
  refine ⟨L, ?_⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  rw [hL 0 hzero]
  change (u 0).val = datumFourierCoeff a
  have hu0 : u 0 = v ⟨0, hzero⟩ := dif_pos hzero
  rw [hu0]
  exact canonicalSobolevLimit_initial_coeff ν hν a ha T hT.le v φ hφ hv

end
end MethbokeAddon.WeakFouriermanB
