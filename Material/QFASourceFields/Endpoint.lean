import QFASourceCoordinates.Endpoint

/-!
# Exact pointwise transport of spatial vector fields

This module transports spatial vector fields through the exact accepted coordinate equivalence
from `QFASourceCoordinates`. It proves both pointwise inverse laws and exact physical Euclidean
norm transport. The separate raw-source `L²` admission is intentionally isolated to a later
package because the pinned Mathlib environment exposes distinct finite-Pi topology and measurable
instances for the raw carrier.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

namespace MethbokeAddon.QuasiFeffermanA.SourceFields

open MethbokeAddon.QuasiFeffermanA.SourceCoordinates

/-- A raw source-coordinate spatial vector field. -/
abbrev SourceVectorField := SourceVec3 → SourceVec3

/-- Pull an arbitrary native Euclidean-valued function back to raw source coordinates. -/
def sourceFieldFunctionOfNative (a : Space → Space) : SourceVectorField :=
  fun x => nativeToSource (a (sourceToNative x))

/-- Push a raw source-coordinate field to a native Euclidean-valued function. -/
def nativeFieldFunctionOfSource (a : SourceVectorField) : Space → Space :=
  fun x => sourceToNative (a (nativeToSource x))

@[simp] theorem sourceFieldFunctionOfNative_apply
    (a : Space → Space) (x : SourceVec3) :
    sourceFieldFunctionOfNative a x = nativeToSource (a (sourceToNative x)) := rfl

@[simp] theorem nativeFieldFunctionOfSource_apply
    (a : SourceVectorField) (x : Space) :
    nativeFieldFunctionOfSource a x = sourceToNative (a (nativeToSource x)) := rfl

@[simp] theorem nativeFieldFunctionOfSource_sourceFieldFunctionOfNative
    (a : Space → Space) (x : Space) :
    nativeFieldFunctionOfSource (sourceFieldFunctionOfNative a) x = a x := by
  simp [nativeFieldFunctionOfSource, sourceFieldFunctionOfNative]

@[simp] theorem sourceFieldFunctionOfNative_nativeFieldFunctionOfSource
    (a : SourceVectorField) (x : SourceVec3) :
    sourceFieldFunctionOfNative (nativeFieldFunctionOfSource a) x = a x := by
  simp [nativeFieldFunctionOfSource, sourceFieldFunctionOfNative]

/-- The source physical Euclidean norm of the pulled-back field is exactly the native pointwise
Euclidean norm. -/
theorem sourceFieldOfNative_euclideanNorm (a : Space → Space) (x : SourceVec3) :
    sourceEuclideanNorm (sourceFieldFunctionOfNative a x) = ‖a (sourceToNative x)‖ := by
  rw [sourceEuclideanNorm_eq_native_norm]
  simp [sourceFieldFunctionOfNative]

/-- The native norm of a pushed-forward source field is exactly its source physical Euclidean
norm. -/
theorem nativeFieldOfSource_norm (a : SourceVectorField) (x : Space) :
    ‖nativeFieldFunctionOfSource a x‖ = sourceEuclideanNorm (a (nativeToSource x)) := by
  symm
  exact sourceEuclideanNorm_eq_native_norm _

end MethbokeAddon.QuasiFeffermanA.SourceFields
