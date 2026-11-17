import MathlibAnalytic.Endpoint

set_option pp.universes true
set_option pp.width 120

#eval IO.println "TYPE_BEGIN:AnalyticAt"
#check @AnalyticAt
#eval IO.println "TYPE_END:AnalyticAt"
#eval IO.println "AXIOMS_BEGIN:AnalyticAt"
#print axioms AnalyticAt
#eval IO.println "AXIOMS_END:AnalyticAt"

#eval IO.println "TYPE_BEGIN:AnalyticOnNhd"
#check @AnalyticOnNhd
#eval IO.println "TYPE_END:AnalyticOnNhd"
#eval IO.println "AXIOMS_BEGIN:AnalyticOnNhd"
#print axioms AnalyticOnNhd
#eval IO.println "AXIOMS_END:AnalyticOnNhd"

#eval IO.println "TYPE_BEGIN:AnalyticOnNhd.mono"
#check @AnalyticOnNhd.mono
#eval IO.println "TYPE_END:AnalyticOnNhd.mono"
#eval IO.println "AXIOMS_BEGIN:AnalyticOnNhd.mono"
#print axioms AnalyticOnNhd.mono
#eval IO.println "AXIOMS_END:AnalyticOnNhd.mono"

#eval IO.println "TYPE_BEGIN:HasFPowerSeriesOnBall.uniform_geometric_approx"
#check @HasFPowerSeriesOnBall.uniform_geometric_approx
#eval IO.println "TYPE_END:HasFPowerSeriesOnBall.uniform_geometric_approx"
#eval IO.println "AXIOMS_BEGIN:HasFPowerSeriesOnBall.uniform_geometric_approx"
#print axioms HasFPowerSeriesOnBall.uniform_geometric_approx
#eval IO.println "AXIOMS_END:HasFPowerSeriesOnBall.uniform_geometric_approx"

#eval IO.println "TYPE_BEGIN:AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq"
#check @AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#eval IO.println "TYPE_END:AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq"
#eval IO.println "AXIOMS_BEGIN:AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq"
#print axioms AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#eval IO.println "AXIOMS_END:AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq"

#eval IO.println "TYPE_BEGIN:AnalyticOnNhd.contDiffOn_of_completeSpace"
#check @AnalyticOnNhd.contDiffOn_of_completeSpace
#eval IO.println "TYPE_END:AnalyticOnNhd.contDiffOn_of_completeSpace"
#eval IO.println "AXIOMS_BEGIN:AnalyticOnNhd.contDiffOn_of_completeSpace"
#print axioms AnalyticOnNhd.contDiffOn_of_completeSpace
#eval IO.println "AXIOMS_END:AnalyticOnNhd.contDiffOn_of_completeSpace"

#eval IO.println "TYPE_BEGIN:contDiffOn_of_locally_contDiffOn"
#check @contDiffOn_of_locally_contDiffOn
#eval IO.println "TYPE_END:contDiffOn_of_locally_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:contDiffOn_of_locally_contDiffOn"
#print axioms contDiffOn_of_locally_contDiffOn
#eval IO.println "AXIOMS_END:contDiffOn_of_locally_contDiffOn"
