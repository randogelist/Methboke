import QFASourceL2.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.SourceCoordinates
open MethbokeAddon.QuasiFeffermanA.SourceFields
open MethbokeAddon.QuasiFeffermanA.SourceL2

namespace QFASourceL2.IndependentTypeChecks

example : Type := SourceSpatialL2

example (a : SpatialL2) :
    MemLp (sourceFieldFunctionOfNative a) (2 : ℝ≥0∞)
      (volume : Measure SourceVec3) :=
  sourceFieldFunctionOfNative_memLp a

example (a : SpatialL2) :
    AEStronglyMeasurable (sourceFieldFunctionOfNative a)
      (volume : Measure SourceVec3) :=
  sourceFieldFunctionOfNative_aestronglyMeasurable a

example (a : SpatialL2) : SourceSpatialL2 :=
  sourceSpatialL2OfNative a

example (a : SpatialL2) :
    (sourceSpatialL2OfNative a : SourceVec3 → SourceVec3)
      =ᵐ[volume] sourceFieldFunctionOfNative a :=
  sourceSpatialL2OfNative_coeFn a

example (a : SourceVectorField)
    (ha : MemLp a (2 : ℝ≥0∞) (volume : Measure SourceVec3)) :
    MemLp (nativeFieldFunctionOfSource a) (2 : ℝ≥0∞)
      (volume : Measure Space) :=
  nativeFieldFunctionOfSource_memLp a ha

example (a : SourceVectorField) :
    MemLp a (2 : ℝ≥0∞) (volume : Measure SourceVec3) ↔
      MemLp (nativeFieldFunctionOfSource a) (2 : ℝ≥0∞)
        (volume : Measure Space) :=
  sourceField_memLp_iff_nativeField_memLp a

end QFASourceL2.IndependentTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.SourceSpatialL2"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.SourceSpatialL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.SourceSpatialL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.SourceSpatialL2"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.SourceSpatialL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.SourceSpatialL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_memLp"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_memLp
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_memLp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_memLp"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_memLp
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_memLp"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_aestronglyMeasurable"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_aestronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_aestronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_aestronglyMeasurable"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_aestronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceFieldFunctionOfNative_aestronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative_coeFn"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative_coeFn
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative_coeFn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative_coeFn"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative_coeFn
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceSpatialL2OfNative_coeFn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.nativeFieldFunctionOfSource_memLp"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.nativeFieldFunctionOfSource_memLp
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.nativeFieldFunctionOfSource_memLp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.nativeFieldFunctionOfSource_memLp"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.nativeFieldFunctionOfSource_memLp
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.nativeFieldFunctionOfSource_memLp"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceField_memLp_iff_nativeField_memLp"
#check @MethbokeAddon.QuasiFeffermanA.SourceL2.sourceField_memLp_iff_nativeField_memLp
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceField_memLp_iff_nativeField_memLp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceField_memLp_iff_nativeField_memLp"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceL2.sourceField_memLp_iff_nativeField_memLp
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceL2.sourceField_memLp_iff_nativeField_memLp"
