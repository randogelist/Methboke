import QFARepresentation.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

/-! Fresh external exact-type and theorem-level axiom audit.
All input hypotheses remain part of each audited statement. -/

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.dense_span_compactSchwartzTests"
#check @QFA.Endpoints.Representation.CompactSchwartz.dense_span_compactSchwartzTests
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.dense_span_compactSchwartzTests"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.dense_span_compactSchwartzTests"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.dense_span_compactSchwartzTests
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.dense_span_compactSchwartzTests"

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.tempered_eq_of_eq_on_compactSchwartz"
#check @QFA.Endpoints.Representation.CompactSchwartz.tempered_eq_of_eq_on_compactSchwartz
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.tempered_eq_of_eq_on_compactSchwartz"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.tempered_eq_of_eq_on_compactSchwartz"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.tempered_eq_of_eq_on_compactSchwartz
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.tempered_eq_of_eq_on_compactSchwartz"

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz"
#check @QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz"

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.correctedCompactToSchwartzEndpoint"
#check @QFA.Endpoints.Representation.CompactSchwartz.correctedCompactToSchwartzEndpoint
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.correctedCompactToSchwartzEndpoint"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.correctedCompactToSchwartzEndpoint"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.correctedCompactToSchwartzEndpoint
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.correctedCompactToSchwartzEndpoint"

#eval IO.println "TYPE_BEGIN:SchwartzMap.qfa_dense_hasCompactSupport"
#check @SchwartzMap.qfa_dense_hasCompactSupport
#eval IO.println "TYPE_END:SchwartzMap.qfa_dense_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:SchwartzMap.qfa_dense_hasCompactSupport"
#print axioms SchwartzMap.qfa_dense_hasCompactSupport
#eval IO.println "AXIOMS_END:SchwartzMap.qfa_dense_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests"
#check @QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests"

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional"
#check @QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional"

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint"
#check @QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint"
#eval IO.println "AXIOMS_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint
#eval IO.println "AXIOMS_END:QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint"

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integrable_norm_sq"
#check @QFA.LC001SpectralReduction.integrable_norm_sq
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integrable_norm_sq"
#eval IO.println "AXIOMS_BEGIN:QFA.LC001SpectralReduction.integrable_norm_sq"
#print axioms QFA.LC001SpectralReduction.integrable_norm_sq
#eval IO.println "AXIOMS_END:QFA.LC001SpectralReduction.integrable_norm_sq"

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq"
#check @QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq"
#eval IO.println "AXIOMS_BEGIN:QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq"
#print axioms QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq
#eval IO.println "AXIOMS_END:QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq"

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integrable_gradient_fourier_sum"
#check @QFA.LC001SpectralReduction.integrable_gradient_fourier_sum
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integrable_gradient_fourier_sum"
#eval IO.println "AXIOMS_BEGIN:QFA.LC001SpectralReduction.integrable_gradient_fourier_sum"
#print axioms QFA.LC001SpectralReduction.integrable_gradient_fourier_sum
#eval IO.println "AXIOMS_END:QFA.LC001SpectralReduction.integrable_gradient_fourier_sum"

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integral_gradient_fourier_sum"
#check @QFA.LC001SpectralReduction.integral_gradient_fourier_sum
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integral_gradient_fourier_sum"
#eval IO.println "AXIOMS_BEGIN:QFA.LC001SpectralReduction.integral_gradient_fourier_sum"
#print axioms QFA.LC001SpectralReduction.integral_gradient_fourier_sum
#eval IO.println "AXIOMS_END:QFA.LC001SpectralReduction.integral_gradient_fourier_sum"

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE"
#check @QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE"
#eval IO.println "AXIOMS_BEGIN:QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE"
#print axioms QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE
#eval IO.println "AXIOMS_END:QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE"

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint"
#check @QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint"
#eval IO.println "AXIOMS_BEGIN:QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint"
#print axioms QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint
#eval IO.println "AXIOMS_END:QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint"

