import QFA
import QFACorrectedRoot

/-!
Passive anchor check preparation. NOT EXECUTED.
Pinned Methlib QFA CorrectedPhysicalRoot package and its existing local package dependencies. Do not overlay duplicate QFA source trees.
Only a later authorized external cached environment may execute this file.
No new theorem or analytic witness is defined. Full theorem parameters remain material.
- Research source inspection does not establish A-tier.
-/

set_option pp.all true
set_option pp.universes true

#check @QFA.Endpoints.Representation.complexifyL2LI
#print axioms QFA.Endpoints.Representation.complexifyL2LI

#check @QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative
#print axioms QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative

#check @QFA.Energy.envelope_product_integral
#print axioms QFA.Energy.envelope_product_integral

#check @QFA.Energy.product_budget
#print axioms QFA.Energy.product_budget

#check @QFA.Energy.product_budget_Ioo
#print axioms QFA.Energy.product_budget_Ioo

#check @QFA.Representation.EnergyProfile.energy_product_budget_Ioo
#print axioms QFA.Representation.EnergyProfile.energy_product_budget_Ioo

#check @QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt
#print axioms QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt

#check @QFA.Endpoints.Restart.strong_right_trace_of_energy_start
#print axioms QFA.Endpoints.Restart.strong_right_trace_of_energy_start

#check @QFA.Assembly.Restart.restartData_of_energyStart
#print axioms QFA.Assembly.Restart.restartData_of_energyStart

#check @QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy
#print axioms QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy

#check @QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton
#print axioms QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton

#check @QFA.Assembly.Chain.ClassRealization
#print axioms QFA.Assembly.Chain.ClassRealization

#check @QFA.Assembly.Chain.ReferencePorts
#print axioms QFA.Assembly.Chain.ReferencePorts

#check @QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption
#print axioms QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption

#check @SchwartzMap.qfa_dense_hasCompactSupport
#print axioms SchwartzMap.qfa_dense_hasCompactSupport

#check @QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional
#print axioms QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional

#check @QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption
#print axioms QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption

#check @QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED
#print axioms QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED
