import QuasiFeffermanB.Endpoints.LerayHopfExistence
import QuasiFeffermanB.Endpoints.CaloricBudget
import QuasiFeffermanB.TailChain

/-! QFB endpoint extraction R4. Deterministic composition into the original
root statement. Candidate only: matching external compilation and a
theorem-level axiom audit are required for promotion. -/

set_option autoImplicit false
set_option Elab.async true

namespace QuasiFeffermanB
open SingularClosure

theorem QUASI_FEFFERMAN_B_COMPOSED : QuasiFeffermanBStatement :=
  Quasi_Fefferman_B_of_LH_existence Q01_LERAY_HOPF_EXISTENCE

end QuasiFeffermanB

/-! Fresh verification of this independently elaborated single-file cutout. -/

set_option pp.universes true
set_option pp.width 120

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED"
#check @QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
#eval IO.println "TYPE_END:QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED"
#eval IO.println "AXIOMS_BEGIN:QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED"
#print axioms QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
#eval IO.println "AXIOMS_END:QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED"

example : QuasiFeffermanB.QuasiFeffermanBStatement :=
  QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
