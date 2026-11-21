import QFASourceCoordinates.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open MeasureTheory
open scoped BigOperators
open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.SourceCoordinates

namespace QFASourceCoordinates.IndependentTypeChecks

example : Type := SourceVec3

example : SourceVec3 ≃L[ℝ] Space := sourceNativeEquiv

example (x : SourceVec3) : Space := sourceToNative x

example (x : Space) : SourceVec3 := nativeToSource x

example (x : SourceVec3) : sourceNativeEquiv x = sourceToNative x :=
  sourceNativeEquiv_apply x

example (x : Space) : sourceNativeEquiv.symm x = nativeToSource x :=
  sourceNativeEquiv_symm_apply x

example (x : Space) : sourceToNative (nativeToSource x) = x :=
  sourceToNative_nativeToSource x

example (x : SourceVec3) : nativeToSource (sourceToNative x) = x :=
  nativeToSource_sourceToNative x

example : MeasurePreserving sourceToNative :=
  sourceToNative_measurePreserving

example : MeasurePreserving nativeToSource :=
  nativeToSource_measurePreserving

example (x : SourceVec3) : ℝ := sourceEuclideanNorm x

example (x : SourceVec3) : sourceEuclideanNorm x = ‖sourceToNative x‖ :=
  sourceEuclideanNorm_eq_native_norm x

example (x : SourceVec3) :
    ‖sourceToNative x‖ ^ 2 = ∑ i : Fin 3, x i ^ 2 :=
  sourceToNative_norm_sq x

example (j : Fin 3) : SourceVec3 := sourceCoordinateVector j

example (j : Fin 3) :
    sourceToNative (sourceCoordinateVector j) = coordinateVector j :=
  sourceToNative_coordinateVector j

end QFASourceCoordinates.IndependentTypeChecks
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.SourceVec3"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.SourceVec3
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.SourceVec3"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.SourceVec3"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.SourceVec3
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.SourceVec3"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_apply"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_symm_apply"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_symm_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_symm_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_symm_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_symm_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceNativeEquiv_symm_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_nativeToSource"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_nativeToSource
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_nativeToSource"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_nativeToSource"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_nativeToSource
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_nativeToSource"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_sourceToNative"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_sourceToNative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_sourceToNative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_sourceToNative"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_sourceToNative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_sourceToNative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_measurePreserving"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_measurePreserving
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_measurePreserving"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_measurePreserving"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_measurePreserving
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_measurePreserving"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_measurePreserving"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_measurePreserving
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_measurePreserving"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_measurePreserving"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_measurePreserving
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.nativeToSource_measurePreserving"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm_eq_native_norm"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm_eq_native_norm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm_eq_native_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm_eq_native_norm"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm_eq_native_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceEuclideanNorm_eq_native_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceCoordinateVector"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceCoordinateVector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceCoordinateVector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceCoordinateVector"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceCoordinateVector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceCoordinateVector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_coordinateVector"
#check @MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_coordinateVector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_coordinateVector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_coordinateVector"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_coordinateVector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceCoordinates.sourceToNative_coordinateVector"
