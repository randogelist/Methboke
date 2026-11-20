import MethbokeAddon.FDSNR3.CompactSchwartz
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Order.Compact

/-!
# A genuine smooth temperate localization of the seed

A compact time cutoff inside the regular interval turns the original seed
into a globally smooth function with polynomial bounds for every actual
joint derivative. The bounds use the seed's existing zeroth spatial weight
and the native iterated-derivative Leibniz inequality. Off the time carrier,
all derivatives vanish by locality.

The cutoff construction has a plateau on a neighborhood of the prescribed
closed interval, so the seed and its localization agree there with all jets.

Prepared without local Lean execution. External compilation and explicit
type/axiom audits are required before acceptance.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

def localizedSeed (χ : ℝ → ℝ) (u : Velocity) : Velocity :=
  fun t x => χ t • u t x

theorem localizedSeed_eq_zero_off_support (χ : ℝ → ℝ) (u : Velocity)
    {t : ℝ} (ht : t ∉ tsupport χ) : localizedSeed χ u t = 0 := by
  funext x
  simp only [localizedSeed, image_eq_zero_of_notMem_tsupport ht, zero_smul, Pi.zero_apply]

theorem localizedSeed_eventuallyEq_zero_off_support (χ : ℝ → ℝ) (u : Velocity)
    {t : ℝ} (ht : t ∉ tsupport χ) (x : Vec) :
    (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun _ => (0 : Vec)) := by
  have hnot : ∀ᶠ z : ℝ × Vec in 𝓝 (t, x), z.1 ∉ tsupport χ :=
    ((isClosed_tsupport χ).isOpen_compl.preimage continuous_fst).mem_nhds ht
  filter_upwards [hnot] with z hz
  exact congrFun (localizedSeed_eq_zero_off_support χ u hz) z.2

theorem localizedSeed_iteratedFDeriv_eq_zero_off_support
    (χ : ℝ → ℝ) (u : Velocity) (n : ℕ) {t : ℝ}
    (ht : t ∉ tsupport χ) (x : Vec) :
    iteratedFDeriv ℝ n (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) (t, x) = 0 := by
  have h := ((localizedSeed_eventuallyEq_zero_off_support χ u ht x).iteratedFDeriv ℝ n).eq_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using h

theorem localizedSeed_eq_of_eq_one {χ : ℝ → ℝ} (u : Velocity)
    {t : ℝ} (ht : χ t = 1) : localizedSeed χ u t = u t := by
  funext x
  simp only [localizedSeed, ht, one_smul]

theorem localizedSeed_eventuallyEq_of_eventuallyEq_one {χ : ℝ → ℝ}
    (u : Velocity) {t : ℝ} (ht : χ =ᶠ[𝓝 t] (fun _ => (1 : ℝ))) (x : Vec) :
    (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z : ℝ × Vec => u z.1 z.2) := by
  have hχ : ∀ᶠ z : ℝ × Vec in 𝓝 (t, x), χ z.1 = 1 :=
    (continuous_fst.tendsto (t, x)).eventually ht
  filter_upwards [hχ] with z hz
  exact congrFun (localizedSeed_eq_of_eq_one u hz) z.2

theorem localizedSeed_iteratedFDeriv_eq_of_eventuallyEq_one {χ : ℝ → ℝ}
    (u : Velocity) {t : ℝ} (ht : χ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)))
    (x : Vec) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) (t, x) =
      iteratedFDeriv ℝ n (fun z : ℝ × Vec => u z.1 z.2) (t, x) :=
  ((localizedSeed_eventuallyEq_of_eventuallyEq_one u ht x).iteratedFDeriv ℝ n).eq_of_nhds

theorem LocalSchwartz.contDiff_localizedSeed {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupport : tsupport χ ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases ht : z.1 ∈ tsupport χ
  · have hn : preterminalSpacetime T ∈ 𝓝 z := by
      have ho : {w : ℝ × Vec | w.1 ∈ Ioo (0 : ℝ) T} ∈ 𝓝 z :=
        (isOpen_Ioo.preimage continuous_fst).mem_nhds (hsupport ht)
      exact Filter.mem_of_superset ho (fun w hw => ⟨hw.1.le, hw.2⟩)
    exact ((hχ.comp contDiff_fst).contDiffAt).smul (hu.1.contDiffAt hn)
  · exact (contDiffAt_const (c := (0 : Vec))).congr_of_eventuallyEq
      (localizedSeed_eventuallyEq_zero_off_support χ u ht z.2)

/-- A smooth compact time cutoff inside the regular interval produces
actual global temperate growth. The source is never extended by an assumed
smoothness or decay certificate. -/
theorem LocalSchwartz.hasTemperateGrowth_localizedSeed {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsupport : tsupport χ ⊆ Ioo (0 : ℝ) T) :
    Function.HasTemperateGrowth (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) := by
  classical
  rcases eq_empty_or_nonempty (tsupport χ) with hempty | hnonempty
  · have hz : (fun z : ℝ × Vec => localizedSeed χ u z.1 z.2) =
        (fun _ => (0 : Vec)) := by
      funext z
      exact congrFun (localizedSeed_eq_zero_off_support χ u (t := z.1) (by simpa [hempty])) z.2
    rw [hz]
    exact Function.HasTemperateGrowth.zero
  obtain ⟨b, hb, hmax⟩ := hcχ.isCompact.exists_isMaxOn hnonempty continuous_id.continuousOn
  have hbT : b ∈ Ico (0 : ℝ) T := ⟨(hsupport hb).1.le, (hsupport hb).2⟩
  have hkernel : Function.HasTemperateGrowth (fun z : ℝ × Vec => χ z.1) :=
    (hcχ.hasTemperateGrowth hχ).comp (ContinuousLinearMap.fst ℝ ℝ Vec).hasTemperateGrowth
  refine ⟨hu.contDiff_localizedSeed hχ hsupport, ?_⟩
  intro n
  obtain ⟨k, C, hC, hkernel_bound⟩ := hkernel.norm_iteratedFDeriv_le_uniform n
  choose D hDnonneg hD using (fun j : ℕ => hu.2 b hbT 0 j)
  let B : ℝ →L[ℝ] Vec →L[ℝ] Vec := ContinuousLinearMap.lsmul ℝ ℝ
  let K : ℝ := ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * D (n - i)
  have hK : 0 ≤ K := by
    apply mul_nonneg (norm_nonneg B)
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (hDnonneg (n - i))
  refine ⟨k, K, ?_⟩
  intro z
  by_cases ht : z.1 ∈ tsupport χ
  · have hz : z ∈ preterminalSpacetime T := ⟨(hsupport ht).1.le, (hsupport ht).2⟩
    have hnhood : preterminalSpacetime T ∈ 𝓝 z := by
      have ho : {w : ℝ × Vec | w.1 ∈ Ioo (0 : ℝ) T} ∈ 𝓝 z :=
        (isOpen_Ioo.preimage continuous_fst).mem_nhds (hsupport ht)
      exact Filter.mem_of_superset ho (fun w hw => ⟨hw.1.le, hw.2⟩)
    have hsets : preterminalSpacetime T =ᶠ[𝓝 z] (univ : Set (ℝ × Vec)) :=
      Filter.eventuallyEq_univ.mpr hnhood
    have htime : z.1 ∈ Icc (0 : ℝ) b := ⟨(hsupport ht).1.le, hmax ht⟩
    have hsource (j : ℕ) :
        ‖iteratedFDerivWithin ℝ j (fun w : ℝ × Vec => u w.1 w.2)
          (preterminalSpacetime T) z‖ ≤ D j := by
      simpa only [weightedJetWithin, pow_zero, one_mul] using hD j z.1 htime z.2
    have hcutoff (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDerivWithin ℝ i (fun w : ℝ × Vec => χ w.1)
          (preterminalSpacetime T) z‖ ≤ C * (1 + ‖z‖) ^ k := by
      rw [iteratedFDerivWithin_congr_set hsets i, iteratedFDerivWithin_univ]
      exact hkernel_bound i hi z
    have hn : (n : ℕ∞ω) ≤ ∞ := by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
    calc
      ‖iteratedFDeriv ℝ n (fun w : ℝ × Vec => localizedSeed χ u w.1 w.2) z‖ =
          ‖iteratedFDerivWithin ℝ n (fun w : ℝ × Vec => B (χ w.1) (u w.1 w.2))
            (preterminalSpacetime T) z‖ := by
        rw [iteratedFDerivWithin_congr_set hsets n, iteratedFDerivWithin_univ]
        rfl
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun w : ℝ × Vec => χ w.1)
            (preterminalSpacetime T) z‖ *
          ‖iteratedFDerivWithin ℝ (n - i) (fun w : ℝ × Vec => u w.1 w.2)
            (preterminalSpacetime T) z‖ :=
        B.norm_iteratedFDerivWithin_le_of_bilinear hkernel.1.contDiffOn hu.1
          (uniqueDiffOn_preterminalSpacetime T) hz hn
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (C * (1 + ‖z‖) ^ k) * D (n - i) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcutoff i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
            (Nat.cast_nonneg _))
          (hsource (n - i)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC (by positivity)))
      _ = ‖B‖ * ((∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * C * D (n - i)) * (1 + ‖z‖) ^ k) := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = K * (1 + ‖z‖) ^ k := by dsimp [K]; ring
  · rw [localizedSeed_iteratedFDeriv_eq_zero_off_support χ u n ht z.2, norm_zero]
    exact mul_nonneg hK (by positivity)

/-- A compact time cutoff with a genuine open plateau around the entire
closed interval. Its support remains strictly inside the regular interval. -/
theorem exists_timeCutoff_for_interval {a b T : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo (0 : ℝ) T ∧
      ∀ t ∈ Icc a b, χ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
  let δ : ℝ := min a (T - b) / 4
  have hδ : 0 < δ := div_pos (lt_min ha (sub_pos.mpr hb)) (by norm_num)
  have hδa : 2 * δ < a := by
    dsimp [δ]
    linarith [min_le_left a (T - b)]
  have hδb : 2 * δ < T - b := by
    dsimp [δ]
    linarith [min_le_right a (T - b)]
  let c : ℝ := (a + b) / 2
  let φ : ContDiffBump c :=
    { rIn := (b - a) / 2 + δ
      rOut := (b - a) / 2 + 2 * δ
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, ?_⟩
  · intro t ht
    rw [φ.tsupport_eq] at ht
    change dist t c ≤ (b - a) / 2 + 2 * δ at ht
    rw [Real.dist_eq] at ht
    obtain ⟨hl, hr⟩ := abs_le.mp ht
    dsimp [c] at hl hr
    constructor <;> linarith
  · intro t ht
    apply φ.eventuallyEq_one_of_mem_ball
    change dist t c < (b - a) / 2 + δ
    rw [Real.dist_eq, abs_lt]
    dsimp [c]
    constructor <;> linarith [ht.1, ht.2]

end

end MethbokeAddon.FDSNR3
