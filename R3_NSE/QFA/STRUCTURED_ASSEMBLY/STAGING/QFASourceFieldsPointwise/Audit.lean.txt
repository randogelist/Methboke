import QFASourceFields.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.SourceCoordinates
open MethbokeAddon.QuasiFeffermanA.SourceFields

namespace QFASourceFields.IndependentTypeChecks

example : Type := SourceVectorField
example (a : Space → Space) : SourceVectorField := sourceFieldFunctionOfNative a
example (a : SourceVectorField) : Space → Space := nativeFieldFunctionOfSource a
example (a : Space → Space) (x : SourceVec3) :
    sourceFieldFunctionOfNative a x = nativeToSource (a (sourceToNative x)) :=
  sourceFieldFunctionOfNative_apply a x
example (a : SourceVectorField) (x : Space) :
    nativeFieldFunctionOfSource a x = sourceToNative (a (nativeToSource x)) :=
  nativeFieldFunctionOfSource_apply a x
example (a : Space → Space) (x : Space) :
    nativeFieldFunctionOfSource (sourceFieldFunctionOfNative a) x = a x :=
  nativeFieldFunctionOfSource_sourceFieldFunctionOfNative a x
example (a : SourceVectorField) (x : SourceVec3) :
    sourceFieldFunctionOfNative (nativeFieldFunctionOfSource a) x = a x :=
  sourceFieldFunctionOfNative_nativeFieldFunctionOfSource a x
example (a : Space → Space) (x : SourceVec3) :
    sourceEuclideanNorm (sourceFieldFunctionOfNative a x) = ‖a (sourceToNative x)‖ :=
  sourceFieldOfNative_euclideanNorm a x
example (a : SourceVectorField) (x : Space) :
    ‖nativeFieldFunctionOfSource a x‖ = sourceEuclideanNorm (a (nativeToSource x)) :=
  nativeFieldOfSource_norm a x

end QFASourceFields.IndependentTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceVectorField"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.SourceVectorField
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceVectorField"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceVectorField"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.SourceVectorField
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceVectorField"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_apply"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_apply"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_sourceFieldFunctionOfNative"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_sourceFieldFunctionOfNative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_sourceFieldFunctionOfNative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_sourceFieldFunctionOfNative"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_sourceFieldFunctionOfNative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldFunctionOfSource_sourceFieldFunctionOfNative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_nativeFieldFunctionOfSource"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_nativeFieldFunctionOfSource
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_nativeFieldFunctionOfSource"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_nativeFieldFunctionOfSource"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_nativeFieldFunctionOfSource
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldFunctionOfNative_nativeFieldFunctionOfSource"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_euclideanNorm"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_euclideanNorm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_euclideanNorm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_euclideanNorm"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_euclideanNorm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_euclideanNorm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_norm"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_norm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_norm"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_norm"
