import QFASourceTestsBasic.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open Set
open scoped ContDiff
open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.SourceCoordinates
open MethbokeAddon.QuasiFeffermanA.SourceTests

namespace QFASourceTestsBasic.IndependentTypeChecks

example : Type := SourceWeakTestFunction
example : CoeFun SourceWeakTestFunction (fun _ => SourceVec3 → ℝ) :=
  instCoeFunSourceWeakTestFunction
example (φ : SourceWeakTestFunction) : Space → ℝ := nativeTestFunctionOfSource φ
example (φ : SourceWeakTestFunction) (x : Space) :
    nativeTestFunctionOfSource φ x = φ.toFun (nativeToSource x) :=
  nativeTestFunctionOfSource_apply φ x
example (φ : SourceWeakTestFunction) :
    ContDiff ℝ (⊤ : ℕ∞) (nativeTestFunctionOfSource φ) :=
  nativeTestFunctionOfSource_contDiff φ
example (φ : SourceWeakTestFunction) :
    HasCompactSupport (nativeTestFunctionOfSource φ) :=
  nativeTestFunctionOfSource_hasCompactSupport φ

end QFASourceTestsBasic.IndependentTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.SourceWeakTestFunction"
#check @MethbokeAddon.QuasiFeffermanA.SourceTests.SourceWeakTestFunction
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceTests.SourceWeakTestFunction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.SourceWeakTestFunction"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceTests.SourceWeakTestFunction
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceTests.SourceWeakTestFunction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.instCoeFunSourceWeakTestFunction"
#check @MethbokeAddon.QuasiFeffermanA.SourceTests.instCoeFunSourceWeakTestFunction
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceTests.instCoeFunSourceWeakTestFunction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.instCoeFunSourceWeakTestFunction"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceTests.instCoeFunSourceWeakTestFunction
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceTests.instCoeFunSourceWeakTestFunction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource"
#check @MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_apply"
#check @MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_contDiff"
#check @MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_contDiff"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_hasCompactSupport"
#check @MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_hasCompactSupport"
#print axioms MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SourceTests.nativeTestFunctionOfSource_hasCompactSupport"
