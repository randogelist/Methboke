import MethbokeAddon.QuasiFeffermanA.HeatDuhamel
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The actual L2 forcing-to-response operator

The physical Duhamel response descends to the actual Bochner time-L2 forcing
class and takes values in continuous physical L2 paths on the closed window.
Its operator norm is at most sqrt(T), and every response has zero initial
trace. Representative compatibility is proved with the existing a.e.
invariance theorem; no forcing regularity or construction witness is added.

This only packages the preceding actual response. It asserts no spatial
maximal regularity, inhomogeneous derivative equation or nonlinear existence.
Prepared source requires matching external compilation and named audits.
No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator

open HeatDuhamel

private def responseContinuousMap (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ContinuousMap (Icc (0 : ℝ) T) SpatialL2 where
  toFun t := duhamelL2 ν (F : ℝ → SpatialL2) (t : ℝ)
  continuous_toFun :=
    (duhamelL2_continuousOn ν (F : ℝ → SpatialL2) T hT (Lp.memLp F)).domRestrict

private def responseLinearMap (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)) →ₗ[ℝ]
      ContinuousMap (Icc (0 : ℝ) T) SpatialL2 where
  toFun := responseContinuousMap ν T hT
  map_add' F G := by
    ext t
    change duhamelL2 ν ((F + G) : ℝ → SpatialL2) (t : ℝ) =
      duhamelL2 ν (F : ℝ → SpatialL2) (t : ℝ) +
        duhamelL2 ν (G : ℝ → SpatialL2) (t : ℝ)
    calc
      duhamelL2 ν ((F + G) : ℝ → SpatialL2) (t : ℝ) =
          duhamelL2 ν (fun s => F s + G s) (t : ℝ) :=
        duhamelL2_ae_eq ν _ _ T (Lp.coeFn_add F G) (t : ℝ) t.property.1 t.property.2
      _ = _ := duhamelL2_add ν _ _ T (Lp.memLp F) (Lp.memLp G)
        (t : ℝ) t.property.1 t.property.2
  map_smul' c F := by
    ext t
    change duhamelL2 ν ((c • F) : ℝ → SpatialL2) (t : ℝ) =
      c • duhamelL2 ν (F : ℝ → SpatialL2) (t : ℝ)
    calc
      duhamelL2 ν ((c • F) : ℝ → SpatialL2) (t : ℝ) =
          duhamelL2 ν (fun s => c • F s) (t : ℝ) :=
        duhamelL2_ae_eq ν _ _ T (Lp.coeFn_smul c F) (t : ℝ) t.property.1 t.property.2
      _ = _ := duhamelL2_smul ν c _ (t : ℝ)

private theorem responseLinearMap_norm_le (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ‖responseLinearMap ν T hT F‖ ≤ Real.sqrt T * ‖F‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg T) (norm_nonneg F))).mpr
  intro t
  change ‖duhamelL2 ν (F : ℝ → SpatialL2) (t : ℝ)‖ ≤ Real.sqrt T * ‖F‖
  simpa only [Lp.toLp_coeFn] using
    duhamelL2_norm_le_sqrt_mul_lpNorm ν (F : ℝ → SpatialL2) T (Lp.memLp F)
      (t : ℝ) t.property.1 t.property.2

/-- The actual bounded linear response to a time-L2 spatial-L2 forcing class. -/
def duhamelL2Operator (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)) →L[ℝ]
      ContinuousMap (Icc (0 : ℝ) T) SpatialL2 :=
  (responseLinearMap ν T hT).mkContinuous (Real.sqrt T)
    (responseLinearMap_norm_le ν T hT)

/-- Evaluation is the literal physical retarded Bochner integral. -/
theorem duhamelL2Operator_apply (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : Icc (0 : ℝ) T) :
    duhamelL2Operator ν T hT F t =
      ∫ s in (0 : ℝ)..(t : ℝ),
        HeatSemigroup.heatL2 ν ((t : ℝ) - s).toNNReal (F s) :=
  rfl

/-- The forcing quotient has the exact sqrt(T) bound in the continuous-path norm. -/
theorem duhamelL2Operator_norm_le (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    ‖duhamelL2Operator ν T hT‖ ≤ Real.sqrt T :=
  (responseLinearMap ν T hT).mkContinuous_norm_le (Real.sqrt_nonneg T)
    (responseLinearMap_norm_le ν T hT)

/-- Every forcing class produces the actual zero initial trace, including T=0. -/
theorem duhamelL2Operator_zero_trace (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    duhamelL2Operator ν T hT F ⟨0, le_rfl, hT⟩ = 0 := by
  change duhamelL2 ν (F : ℝ → SpatialL2) 0 = 0
  exact duhamelL2_zero_time ν (F : ℝ → SpatialL2)

/-- Every admissible representative gives the same response after passing to
the actual L2 quotient; no pointwise equality of chosen representatives is assumed. -/
theorem duhamelL2Operator_toLp_apply (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → SpatialL2) (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : Icc (0 : ℝ) T) :
    duhamelL2Operator ν T hT (hf.toLp f) t = duhamelL2 ν f (t : ℝ) := by
  change duhamelL2 ν (hf.toLp f : ℝ → SpatialL2) (t : ℝ) = duhamelL2 ν f (t : ℝ)
  exact duhamelL2_ae_eq ν _ _ T hf.coeFn_toLp (t : ℝ) t.property.1 t.property.2

end MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator
