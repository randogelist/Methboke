import QFASourceFields.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open MeasureTheory
open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.SourceCoordinates
open MethbokeAddon.QuasiFeffermanA.SourceFields

namespace QFASourceFields.IndependentTypeChecks

example : Type := SourceVectorField
example : Type := SourceSpatialL2
example (a : Space → Space) : SourceVectorField := sourceFieldFunctionOfNative a
example (a : SourceVectorField) : Space → Space := nativeFieldFunctionOfSource a
example (a : Space → Space) (x : Space) :
    nativeFieldFunctionOfSource (sourceFieldFunctionOfNative a) x = a x :=
  nativeFieldFunctionOfSource_sourceFieldFunctionOfNative a x
example (a : SourceVectorField) (x : SourceVec3) :
    sourceFieldFunctionOfNative (nativeFieldFunctionOfSource a) x = a x :=
  sourceFieldFunctionOfNative_nativeFieldFunctionOfSource a x
example (a : SpatialL2) :
    MemLp (sourceFieldFunctionOfNative a) 2 (volume : Measure SourceVec3) :=
  sourceFieldOfNative_memLp a
example (a : SpatialL2) : SourceSpatialL2 := sourceL2OfNative a
example (a : SpatialL2) :
    (fun x : SourceVec3 => sourceL2OfNative a x) =ᵐ[volume]
      sourceFieldFunctionOfNative a := sourceL2OfNative_ae a
example (a : SourceSpatialL2) :
    MemLp (nativeFieldFunctionOfSource a) 2 (volume : Measure Space) :=
  nativeFieldOfSource_memLp a
example (a : SourceSpatialL2) : SpatialL2 := nativeL2OfSource a
example (a : SourceSpatialL2) :
    (fun x : Space => nativeL2OfSource a x) =ᵐ[volume]
      nativeFieldFunctionOfSource a := nativeL2OfSource_ae a
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

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceSpatialL2"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.SourceSpatialL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceSpatialL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceSpatialL2"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.SourceSpatialL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.SourceSpatialL2"

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

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_memLp"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_memLp
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_memLp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_memLp"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_memLp
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceFieldOfNative_memLp"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative_ae"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.sourceL2OfNative_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_memLp"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_memLp
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_memLp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_memLp"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_memLp
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeFieldOfSource_memLp"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource_ae"
#check @MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceFields.nativeL2OfSource_ae"

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
