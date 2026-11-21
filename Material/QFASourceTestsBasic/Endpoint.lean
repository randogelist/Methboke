import QFASourceFields.Endpoint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-!
# Smooth compact scalar tests on source and native coordinates

This endpoint mirrors the selected CKN weak scalar-test facade on the accepted raw source carrier
and transports each source test to Methboke's native Euclidean carrier. It proves exact function
application, smoothness, and compact support. Coordinate derivatives are intentionally isolated to
a separate calculus endpoint.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set
open scoped ContDiff

namespace MethbokeAddon.QuasiFeffermanA.SourceTests

open MethbokeAddon.QuasiFeffermanA.SourceCoordinates

/-- Source-coordinate counterpart of the selected CKN weak scalar test function. -/
structure SourceWeakTestFunction where
  toFun : SourceVec3 → ℝ
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun

instance instCoeFunSourceWeakTestFunction :
    CoeFun SourceWeakTestFunction (fun _ => SourceVec3 → ℝ) where
  coe φ := φ.toFun

/-- Pull a source scalar test to the native Euclidean carrier. -/
def nativeTestFunctionOfSource (φ : SourceWeakTestFunction) : Space → ℝ :=
  fun x => φ.toFun (nativeToSource x)

@[simp] theorem nativeTestFunctionOfSource_apply
    (φ : SourceWeakTestFunction) (x : Space) :
    nativeTestFunctionOfSource φ x = φ.toFun (nativeToSource x) := rfl

/-- The pulled-back native test is smooth. -/
theorem nativeTestFunctionOfSource_contDiff (φ : SourceWeakTestFunction) :
    ContDiff ℝ (⊤ : ℕ∞) (nativeTestFunctionOfSource φ) := by
  have hfun : nativeTestFunctionOfSource φ = φ.toFun ∘ sourceNativeEquiv.symm := by
    funext x
    simp [nativeTestFunctionOfSource]
  rw [hfun]
  exact φ.contDiff.comp sourceNativeEquiv.symm.contDiff

/-- The pulled-back native test retains compact support. -/
theorem nativeTestFunctionOfSource_hasCompactSupport (φ : SourceWeakTestFunction) :
    HasCompactSupport (nativeTestFunctionOfSource φ) := by
  have hfun : nativeTestFunctionOfSource φ = φ.toFun ∘ sourceNativeEquiv.symm := by
    funext x
    simp [nativeTestFunctionOfSource]
  rw [hfun]
  exact φ.hasCompactSupport.comp_homeomorph sourceNativeEquiv.symm.toHomeomorph

end MethbokeAddon.QuasiFeffermanA.SourceTests
