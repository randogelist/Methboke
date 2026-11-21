import MethbokeAddon.QuasiFeffermanA.Contracts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Exact CKN-source coordinates and native Euclidean coordinates

The CKN source carrier is `Fin 3 → ℝ`.  Methboke's native whole-space
carrier is `EuclideanSpace ℝ (Fin 3)`, definitionally the `L²` Pi wrapper
`WithLp 2 (Fin 3 → ℝ)`.  This endpoint exposes the canonical conversion,
its inverse, exact volume preservation, and exact Euclidean norm formulas.

Mathematical/source provenance:
* scottnarmstrong/CaffarelliKohnNirenberg@
  381d658ead0f03a18361965cc0427ce3fa5844ab,
  `CKN/Foundation/Sobolev/Ambient/Basic.lean` (`CKN.Vec`),
  `CKN/Foundation/Ambient/Euclidean.lean` (`CKN.Space`,
  `CKN.spaceEuclideanNorm`);
* Mathlib@db584cd6d46c92f209a44c0f1c829460d327499d,
  `PiLp.continuousLinearEquiv`, `PiLp.volume_preserving_toLp`,
  `PiLp.volume_preserving_ofLp`, `PiLp.norm_eq_of_L2`, and
  `PiLp.norm_sq_eq_of_L2`.

No CKN proof source is imported and no PDE, existence, regularity,
comparison, sharp Sobolev, or QFA conclusion is asserted.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace MethbokeAddon.QuasiFeffermanA.SourceCoordinates

/-- The exact coordinate carrier used by the selected CKN source. -/
abbrev SourceVec3 := Fin 3 → ℝ

/-- The canonical continuous linear equivalence from raw coordinates to
the native Euclidean carrier. -/
noncomputable def sourceNativeEquiv : SourceVec3 ≃L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

/-- Put raw source coordinates into the native `L²` Pi wrapper. -/
def sourceToNative (x : SourceVec3) : Space := WithLp.toLp 2 x

/-- Forget the native `L²` Pi wrapper and recover raw source coordinates. -/
def nativeToSource (x : Space) : SourceVec3 := WithLp.ofLp x

@[simp] theorem sourceNativeEquiv_apply (x : SourceVec3) :
    sourceNativeEquiv x = sourceToNative x := rfl

@[simp] theorem sourceNativeEquiv_symm_apply (x : Space) :
    sourceNativeEquiv.symm x = nativeToSource x := rfl

@[simp] theorem sourceToNative_nativeToSource (x : Space) :
    sourceToNative (nativeToSource x) = x := rfl

@[simp] theorem nativeToSource_sourceToNative (x : SourceVec3) :
    nativeToSource (sourceToNative x) = x := rfl

/-- Raw-to-native coordinates preserve full Lebesgue volume exactly. -/
theorem sourceToNative_measurePreserving :
    MeasurePreserving sourceToNative := by
  simpa only [sourceToNative] using
    (PiLp.volume_preserving_toLp (Fin 3))

/-- Native-to-raw coordinates preserve full Lebesgue volume exactly. -/
theorem nativeToSource_measurePreserving :
    MeasurePreserving nativeToSource := by
  simpa only [nativeToSource] using
    (PiLp.volume_preserving_ofLp (Fin 3))

/-- The source's finite-coordinate Euclidean norm. -/
noncomputable def sourceEuclideanNorm (x : SourceVec3) : ℝ :=
  Real.sqrt (∑ i : Fin 3, x i ^ 2)

/-- The source Euclidean norm is the native Euclidean norm on the nose. -/
theorem sourceEuclideanNorm_eq_native_norm (x : SourceVec3) :
    sourceEuclideanNorm x = ‖sourceToNative x‖ := by
  unfold sourceEuclideanNorm sourceToNative
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

/-- Exact coordinate sum-of-squares formula for the native norm. -/
theorem sourceToNative_norm_sq (x : SourceVec3) :
    ‖sourceToNative x‖ ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  simpa only [sourceToNative, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (sourceToNative x))

/-- The source coordinate basis vector. -/
def sourceCoordinateVector (j : Fin 3) : SourceVec3 := Pi.single j 1

/-- The source and native coordinate vectors are definitionally the same
after the canonical coordinate conversion. -/
@[simp] theorem sourceToNative_coordinateVector (j : Fin 3) :
    sourceToNative (sourceCoordinateVector j) = coordinateVector j := rfl

end MethbokeAddon.QuasiFeffermanA.SourceCoordinates
