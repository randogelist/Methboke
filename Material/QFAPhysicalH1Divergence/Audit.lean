import QFAPhysicalH1Divergence.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff

namespace QFAPhysicalH1Divergence.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence

example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

example (v : SpatialL2) : Solenoidal v ↔
    ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun x : MethbokeAddon.QuasiFeffermanA.Space =>
        inner ℝ (v x) (scalarGradient ψ x)) volume ∧
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space,
        inner ℝ (v x) (scalarGradient ψ x)) = 0 := Iff.rfl

example (v : SpatialL2) (G : Fin 3 → SpatialL2) : SpatialWeakGradient v G ↔
    ∀ (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space,
        fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • G j x) := Iff.rfl

example (j : Fin 3) : MethbokeAddon.QuasiFeffermanA.Space →L[ℝ]
    MethbokeAddon.QuasiFeffermanA.Space := coordinateSliceVectorCLM j

example (j : Fin 3) (v : MethbokeAddon.QuasiFeffermanA.Space) :
    coordinateSliceVectorCLM j v = (v j) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) :=
  coordinateSliceVectorCLM_apply j v

example (j : Fin 3) : SpatialL2 →L[ℝ] SpatialL2 := coordinateSliceL2 j

example (j : Fin 3) : coordinateSliceL2 j =
    (coordinateSliceVectorCLM j).compLpL 2 volume := rfl

example (j : Fin 3) (v : SpatialL2) :
    (fun x : MethbokeAddon.QuasiFeffermanA.Space => coordinateSliceL2 j v x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space => (v x j) •
        EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := coordinateSliceL2_ae j v

example (G : Fin 3 → SpatialL2) : SpatialL2 := spatialGradientTrace G
example (G : Fin 3 → SpatialL2) : spatialGradientTrace G =
    ∑ j : Fin 3, coordinateSliceL2 j (G j) := rfl

example (G : Fin 3 → SpatialL2) :
    (fun x : MethbokeAddon.QuasiFeffermanA.Space => spatialGradientTrace G x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space =>
        (∑ j : Fin 3, G j x j) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
  spatialGradientTrace_ae G

example (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (v : SpatialL2) :
    compactPairingCLM ψ hψ hc (coordinateSliceL2 j v) =
      coordinateSliceVectorCLM j (compactPairingCLM ψ hψ hc v) :=
  compactPairing_coordinateSlice j ψ hψ hc v

example (v : SpatialL2) (G : Fin 3 → SpatialL2) (hw : SpatialWeakGradient v G)
    (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    compactPairingCLM ψ hψ.continuous hc (spatialGradientTrace G) =
      -((∫ x : MethbokeAddon.QuasiFeffermanA.Space,
        inner ℝ (v x) (scalarGradient ψ x)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
  spatialWeakGradient_trace_pairing hw ψ hψ hc

-- The same native solenoidal condition, no spectral/divergence/sector premise.
example (v : SpatialL2) (G : Fin 3 → SpatialL2) (hw : SpatialWeakGradient v G) :
    Solenoidal v ↔ (∑ j : Fin 3, coordinateSliceL2 j (G j)) = 0 :=
  spatialWeakGradient_solenoidal_iff_trace_eq_zero hw

end QFAPhysicalH1Divergence.ExpectedTypes

-- BEGIN NAMED REPORTS

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceVectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2_ae"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.coordinateSliceL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace_ae"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialGradientTrace_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.compactPairing_coordinateSlice"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.compactPairing_coordinateSlice
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.compactPairing_coordinateSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.compactPairing_coordinateSlice"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.compactPairing_coordinateSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.compactPairing_coordinateSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_trace_pairing"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_trace_pairing
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_trace_pairing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_trace_pairing"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_trace_pairing
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_trace_pairing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_solenoidal_iff_trace_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_solenoidal_iff_trace_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_solenoidal_iff_trace_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_solenoidal_iff_trace_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_solenoidal_iff_trace_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence.spatialWeakGradient_solenoidal_iff_trace_eq_zero"
