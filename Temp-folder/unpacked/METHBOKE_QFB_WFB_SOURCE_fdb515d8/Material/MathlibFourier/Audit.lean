import MathlibFourier.Endpoint

set_option pp.universes true

#eval IO.println "TYPE_BEGIN:UnitAddTorus.mFourierBasis"
#check @UnitAddTorus.mFourierBasis
#eval IO.println "TYPE_END:UnitAddTorus.mFourierBasis"
#eval IO.println "AXIOMS_BEGIN:UnitAddTorus.mFourierBasis"
#print axioms UnitAddTorus.mFourierBasis
#eval IO.println "AXIOMS_END:UnitAddTorus.mFourierBasis"

#eval IO.println "TYPE_BEGIN:UnitAddTorus.hasSum_mFourier_series_L2"
#check @UnitAddTorus.hasSum_mFourier_series_L2
#eval IO.println "TYPE_END:UnitAddTorus.hasSum_mFourier_series_L2"
#eval IO.println "AXIOMS_BEGIN:UnitAddTorus.hasSum_mFourier_series_L2"
#print axioms UnitAddTorus.hasSum_mFourier_series_L2
#eval IO.println "AXIOMS_END:UnitAddTorus.hasSum_mFourier_series_L2"

#eval IO.println "TYPE_BEGIN:UnitAddTorus.hasSum_sq_mFourierCoeff"
#check @UnitAddTorus.hasSum_sq_mFourierCoeff
#eval IO.println "TYPE_END:UnitAddTorus.hasSum_sq_mFourierCoeff"
#eval IO.println "AXIOMS_BEGIN:UnitAddTorus.hasSum_sq_mFourierCoeff"
#print axioms UnitAddTorus.hasSum_sq_mFourierCoeff
#eval IO.println "AXIOMS_END:UnitAddTorus.hasSum_sq_mFourierCoeff"
