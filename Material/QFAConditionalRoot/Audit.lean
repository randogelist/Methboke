import QFAConditionalRoot.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

/-! Fresh external exact-type and theorem-level axiom audit.
All input hypotheses remain part of each audited statement. -/

open Set Filter
open scoped Topology
open QFA.Representation QFA.Endpoints.Restart QFA.Assembly.Chain
open QFA.CorrectedPhysicalRoot

namespace QFAConditionalRoot.TypeChecks

-- Literal historical conclusion, including its historical strict cutoff.
example (ν : ℝ) (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (SmoothNSETail : ℝ → Trajectory → ℝ → Prop) :
    QFARoot ν Domain Admissible SmoothNSETail ↔
      ∀ a ∈ Domain,
        (Admissible a).Nonempty ∧
        ∀ u ∈ Admissible a,
          Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) ∧
          ∀ δ : ℝ, ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ →
            SmoothNSETail ν u δ ∧
            restrictedAdmissible Admissible (u δ) = {tailRestriction δ u} := Iff.rfl

-- The analytic backend remains a theorem hypothesis with an existence conclusion.
example (ν : ℝ) (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Reference : RealSpatialL2 → Trajectory → Prop)
    (Good : Trajectory → GradientTrajectory → ℝ → Prop) :
    CorrectedReferenceConstructionFromAbsorption ν Domain Admissible Reference Good ↔
      (CorrectedPointwiseAbsorption ν →
        SubcriticalReferenceConstruction ν Domain Admissible Reference Good) := Iff.rfl

example {ν : ℝ} {Domain : Set RealSpatialL2}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {Good : Trajectory → GradientTrajectory → ℝ → Prop}
    {SmoothNSETail : ℝ → Trajectory → ℝ → Prop}
    (hν : 0 < ν)
    (hClass : ClassRealization ν Domain Admissible Good)
    (hPorts : ReferencePorts Admissible Reference)
    (hSpectral : QFA.Endpoints.Agmon.WholeSpaceSpectralEndpoint)
    (hAgmon : QFA.Endpoints.Agmon.WholeSpaceAgmonEndpoint)
    (hReferenceBackend :
      CorrectedReferenceConstructionFromAbsorption ν Domain Admissible Reference Good)
    (hSmooth : SmoothReferencePorts ν Reference SmoothNSETail) :
    ∀ a ∈ Domain,
      (Admissible a).Nonempty ∧
      ∀ u ∈ Admissible a,
        Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) ∧
        ∀ δ : ℝ, ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ →
          SmoothNSETail ν u δ ∧
          restrictedAdmissible Admissible (u δ) = {tailRestriction δ u} :=
  QUASI_FEFFERMAN_A_CORRECTED hν hClass hPorts hSpectral hAgmon hReferenceBackend hSmooth

end QFAConditionalRoot.TypeChecks

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData"
#check @QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData"
#print axioms QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs"
#check @QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs"
#print axioms QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.correctedPointwiseAbsorption_of_analytic_inputs"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs"
#check @QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs"
#print axioms QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.quantified_tail_assembly_of_corrected_analytic_inputs"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton"
#check @QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton"
#print axioms QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.selectedTail_restricted_singleton"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.selectedTail_smooth"
#check @QFA.CorrectedPhysicalRoot.selectedTail_smooth
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.selectedTail_smooth"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.selectedTail_smooth"
#print axioms QFA.CorrectedPhysicalRoot.selectedTail_smooth
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.selectedTail_smooth"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion"
#check @QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion"
#print axioms QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.selectedTail_root_conclusion"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED"
#check @QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED"
#print axioms QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.QFARoot"
#check @QFA.CorrectedPhysicalRoot.QFARoot
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.QFARoot"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.QFARoot"
#print axioms QFA.CorrectedPhysicalRoot.QFARoot
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.QFARoot"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.SmoothReferencePorts.mk"
#check @QFA.CorrectedPhysicalRoot.SmoothReferencePorts.mk
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.SmoothReferencePorts.mk"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.SmoothReferencePorts.mk"
#print axioms QFA.CorrectedPhysicalRoot.SmoothReferencePorts.mk
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.SmoothReferencePorts.mk"

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Chain.ClassRealization.mk"
#check @QFA.Assembly.Chain.ClassRealization.mk
#eval IO.println "TYPE_END:QFA.Assembly.Chain.ClassRealization.mk"
#eval IO.println "AXIOMS_BEGIN:QFA.Assembly.Chain.ClassRealization.mk"
#print axioms QFA.Assembly.Chain.ClassRealization.mk
#eval IO.println "AXIOMS_END:QFA.Assembly.Chain.ClassRealization.mk"

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Chain.ReferencePorts.mk"
#check @QFA.Assembly.Chain.ReferencePorts.mk
#eval IO.println "TYPE_END:QFA.Assembly.Chain.ReferencePorts.mk"
#eval IO.println "AXIOMS_BEGIN:QFA.Assembly.Chain.ReferencePorts.mk"
#print axioms QFA.Assembly.Chain.ReferencePorts.mk
#eval IO.println "AXIOMS_END:QFA.Assembly.Chain.ReferencePorts.mk"

#eval IO.println "TYPE_BEGIN:QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption"
#check @QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption
#eval IO.println "TYPE_END:QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption"
#eval IO.println "AXIOMS_BEGIN:QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption"
#print axioms QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption
#eval IO.println "AXIOMS_END:QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption"

