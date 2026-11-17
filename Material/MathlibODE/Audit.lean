import MathlibODE.Endpoint

set_option pp.universes true
set_option pp.width 120

#eval IO.println "TYPE_BEGIN:IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt"
#check @IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#eval IO.println "TYPE_END:IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt"
#eval IO.println "AXIOMS_BEGIN:IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt"
#print axioms IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#eval IO.println "AXIOMS_END:IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt"

#eval IO.println "TYPE_BEGIN:ODE_solution_unique_of_mem_Ioo"
#check @ODE_solution_unique_of_mem_Ioo
#eval IO.println "TYPE_END:ODE_solution_unique_of_mem_Ioo"
#eval IO.println "AXIOMS_BEGIN:ODE_solution_unique_of_mem_Ioo"
#print axioms ODE_solution_unique_of_mem_Ioo
#eval IO.println "AXIOMS_END:ODE_solution_unique_of_mem_Ioo"

#eval IO.println "TYPE_BEGIN:norm_le_gronwallBound_of_norm_deriv_right_le"
#check @norm_le_gronwallBound_of_norm_deriv_right_le
#eval IO.println "TYPE_END:norm_le_gronwallBound_of_norm_deriv_right_le"
#eval IO.println "AXIOMS_BEGIN:norm_le_gronwallBound_of_norm_deriv_right_le"
#print axioms norm_le_gronwallBound_of_norm_deriv_right_le
#eval IO.println "AXIOMS_END:norm_le_gronwallBound_of_norm_deriv_right_le"
