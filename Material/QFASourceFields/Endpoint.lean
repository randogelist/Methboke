import QFASourceCoordinates.Endpoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Exact transport of spatial vector fields between CKN raw coordinates and native Euclidean space

This module transports spatial vector fields through the exact coordinate equivalence from
`QFASourceCoordinates`.  It proves pointwise inverse laws and `L²` membership in both directions.
The source field codomain retains the raw `Fin 3 → ℝ` norm used by CKN's `MemLp` interface;
physical Euclidean norm identities are stated separately and exactly.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory

namespace MethbokeAddon.QuasiFeffermanA.SourceFields

open MethbokeAddon.QuasiFeffermanA.SourceCoordinates

/-- A raw source-coordinate spatial vector field. -/
abbrev SourceVectorField := SourceVec3 → SourceVec3

/-- Source-coordinate spatial `L²`, using the source project's raw finite-Pi norm. -/
abbrev SourceSpatialL2 := Lp SourceVec3 2 (volume : Measure SourceVec3)

/-- Pull an arbitrary native Euclidean-valued function back to raw source coordinates. -/
def sourceFieldFunctionOfNative (a : Space → Space) : SourceVectorField :=
  fun x => nativeToSource (a (sourceToNative x))

/-- Push a raw source-coordinate field to a native Euclidean-valued function. -/
def nativeFieldFunctionOfSource (a : SourceVectorField) : Space → Space :=
  fun x => sourceToNative (a (nativeToSource x))

@[simp] theorem nativeFieldFunctionOfSource_sourceFieldFunctionOfNative
    (a : Space → Space) (x : Space) :
    nativeFieldFunctionOfSource (sourceFieldFunctionOfNative a) x = a x := by
  simp [nativeFieldFunctionOfSource, sourceFieldFunctionOfNative]

@[simp] theorem sourceFieldFunctionOfNative_nativeFieldFunctionOfSource
    (a : SourceVectorField) (x : SourceVec3) :
    sourceFieldFunctionOfNative (nativeFieldFunctionOfSource a) x = a x := by
  simp [nativeFieldFunctionOfSource, sourceFieldFunctionOfNative]

/-- Pulling a native `L²` representative back to source coordinates preserves `L²` membership. -/
theorem sourceFieldOfNative_memLp (a : SpatialL2) :
    MemLp (sourceFieldFunctionOfNative a) 2 (volume : Measure SourceVec3) := by
  have hdom : MemLp (fun x : SourceVec3 => a (sourceToNative x)) 2
      (volume : Measure SourceVec3) := by
    simpa only [Function.comp_apply] using
      (Lp.memLp a).comp_measurePreserving
        (f := sourceToNative) sourceToNative_measurePreserving
  have hout := hdom.continuousLinearMap_comp
    sourceNativeEquiv.symm.toContinuousLinearMap
  simpa only [sourceFieldFunctionOfNative, sourceNativeEquiv_symm_apply] using hout

/-- The actual source-coordinate `L²` class induced by a native spatial `L²` field. -/
noncomputable def sourceL2OfNative (a : SpatialL2) : SourceSpatialL2 :=
  (sourceFieldOfNative_memLp a).toLp (sourceFieldFunctionOfNative a)

/-- The chosen representative of `sourceL2OfNative` agrees almost everywhere with the direct
coordinate pullback. -/
theorem sourceL2OfNative_ae (a : SpatialL2) :
    (fun x : SourceVec3 => sourceL2OfNative a x) =ᵐ[volume]
      sourceFieldFunctionOfNative a :=
  (sourceFieldOfNative_memLp a).coeFn_toLp

/-- Pushing a raw source `L²` representative forward gives a native `L²` function. -/
theorem nativeFieldOfSource_memLp (a : SourceSpatialL2) :
    MemLp (nativeFieldFunctionOfSource a) 2 (volume : Measure Space) := by
  have hdom : MemLp (fun x : Space => a (nativeToSource x)) 2
      (volume : Measure Space) := by
    simpa only [Function.comp_apply] using
      (Lp.memLp a).comp_measurePreserving
        (f := nativeToSource) nativeToSource_measurePreserving
  have hout := hdom.continuousLinearMap_comp
    sourceNativeEquiv.toContinuousLinearMap
  simpa only [nativeFieldFunctionOfSource, sourceNativeEquiv_apply] using hout

/-- The actual native spatial `L²` class induced by a source-coordinate `L²` field. -/
noncomputable def nativeL2OfSource (a : SourceSpatialL2) : SpatialL2 :=
  (nativeFieldOfSource_memLp a).toLp (nativeFieldFunctionOfSource a)

/-- The chosen representative of `nativeL2OfSource` agrees almost everywhere with the direct
coordinate pushforward. -/
theorem nativeL2OfSource_ae (a : SourceSpatialL2) :
    (fun x : Space => nativeL2OfSource a x) =ᵐ[volume]
      nativeFieldFunctionOfSource a :=
  (nativeFieldOfSource_memLp a).coeFn_toLp

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
