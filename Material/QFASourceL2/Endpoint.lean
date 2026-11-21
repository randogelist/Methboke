import QFASourceFields.Endpoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Raw source-coordinate L2 admission

This endpoint transports genuine native `SpatialL2` fields to the raw source-coordinate
function carrier used by the selected CKN interfaces. The domain conversion is exactly
measure preserving, while the finite-dimensional value conversion is transported one
coordinate at a time. Consequently the transported raw function is genuinely in `MemLp 2`.

The reverse qualitative `MemLp` transport is also recorded. These statements concern the
raw finite-product norm used by `MemLp`; exact physical Euclidean norm identities remain in
`QFASourceFields` and are not replaced by a hidden norm identification.

No weak divergence, `IsInJ`, H1 good-time, PDE, existence, comparison, continuation, smooth
solution, sharp Sobolev, or QFA-root conclusion is asserted.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace MethbokeAddon.QuasiFeffermanA.SourceL2

open MethbokeAddon.QuasiFeffermanA.SourceCoordinates
open MethbokeAddon.QuasiFeffermanA.SourceFields

/-- Raw source-coordinate L2 equivalence classes. -/
abbrev SourceSpatialL2 :=
  Lp (α := SourceVec3) SourceVec3 (2 : ℝ≥0∞) (volume : Measure SourceVec3)

/-- Pulling a genuine native spatial L2 class to raw source coordinates gives a genuine
source-coordinate `MemLp 2` function. -/
theorem sourceFieldFunctionOfNative_memLp (a : SpatialL2) :
    MemLp (sourceFieldFunctionOfNative a) (2 : ℝ≥0∞)
      (volume : Measure SourceVec3) := by
  have hcomp :
      MemLp (fun x : SourceVec3 => a (sourceToNative x)) (2 : ℝ≥0∞)
        (volume : Measure SourceVec3) :=
    (Lp.memLp a).comp_measurePreserving sourceToNative_measurePreserving
  apply MemLp.of_eval
  intro i
  have hi := hcomp.eval_piLp i
  simpa [sourceFieldFunctionOfNative, nativeToSource, sourceNativeEquiv] using hi

/-- The transported raw source field is almost-everywhere strongly measurable. -/
theorem sourceFieldFunctionOfNative_aestronglyMeasurable (a : SpatialL2) :
    AEStronglyMeasurable (sourceFieldFunctionOfNative a)
      (volume : Measure SourceVec3) :=
  (sourceFieldFunctionOfNative_memLp a).aestronglyMeasurable

/-- The canonical raw source-coordinate L2 class represented by a native spatial L2 field. -/
noncomputable def sourceSpatialL2OfNative (a : SpatialL2) : SourceSpatialL2 :=
  (sourceFieldFunctionOfNative_memLp a).toLp (sourceFieldFunctionOfNative a)

/-- The canonical source L2 class has the transported raw field as its a.e. representative. -/
theorem sourceSpatialL2OfNative_coeFn (a : SpatialL2) :
    (sourceSpatialL2OfNative a : SourceVec3 → SourceVec3)
      =ᵐ[volume] sourceFieldFunctionOfNative a := by
  exact (sourceFieldFunctionOfNative_memLp a).coeFn_toLp

/-- Pushing a raw source-coordinate `MemLp 2` field to native coordinates preserves
qualitative square integrability. -/
theorem nativeFieldFunctionOfSource_memLp
    (a : SourceVectorField)
    (ha : MemLp a (2 : ℝ≥0∞) (volume : Measure SourceVec3)) :
    MemLp (nativeFieldFunctionOfSource a) (2 : ℝ≥0∞)
      (volume : Measure Space) := by
  have hcomp :
      MemLp (fun x : Space => a (nativeToSource x)) (2 : ℝ≥0∞)
        (volume : Measure Space) :=
    ha.comp_measurePreserving nativeToSource_measurePreserving
  apply MemLp.of_eval_piLp
  intro i
  have hi := hcomp.eval i
  simpa [nativeFieldFunctionOfSource, sourceToNative, sourceNativeEquiv] using hi

/-- Raw source-coordinate square integrability is recovered from square integrability of
the pushed-forward native field. -/
private theorem sourceField_memLp_of_nativeField_memLp
    (a : SourceVectorField)
    (ha : MemLp (nativeFieldFunctionOfSource a) (2 : ℝ≥0∞)
      (volume : Measure Space)) :
    MemLp a (2 : ℝ≥0∞) (volume : Measure SourceVec3) := by
  have hcomp :
      MemLp (fun x : SourceVec3 =>
        nativeFieldFunctionOfSource a (sourceToNative x)) (2 : ℝ≥0∞)
        (volume : Measure SourceVec3) :=
    ha.comp_measurePreserving sourceToNative_measurePreserving
  apply MemLp.of_eval
  intro i
  have hi := hcomp.eval_piLp i
  simpa [nativeFieldFunctionOfSource, sourceToNative, nativeToSource,
    sourceNativeEquiv] using hi

/-- The raw source field is in `MemLp 2` exactly when its pushed-forward native field is. -/
theorem sourceField_memLp_iff_nativeField_memLp (a : SourceVectorField) :
    MemLp a (2 : ℝ≥0∞) (volume : Measure SourceVec3) ↔
      MemLp (nativeFieldFunctionOfSource a) (2 : ℝ≥0∞)
        (volume : Measure Space) :=
  ⟨nativeFieldFunctionOfSource_memLp a,
    sourceField_memLp_of_nativeField_memLp a⟩

end MethbokeAddon.QuasiFeffermanA.SourceL2
