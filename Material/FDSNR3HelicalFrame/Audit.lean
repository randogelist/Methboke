import FDSNR3HelicalFrame.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false
open SingularClosure
open scoped BigOperators ComplexConjugate
open MethbokeAddon.FDSNR3

/- Independent literal consumers for the fixed-frame R3-04 bridge.
   To be appended to the Helical audit after the candidate is integrated. -/

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (b : OrthonormalBasis (Fin 3) ℂ CVec)
    (hcurl : ∀ τ : Fin 2,
      Complex.I • complexCross ξ (b τ.castSucc) =
        ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc)
    (hlong : b 2 = (‖ξ‖ : ℂ)⁻¹ • complexify ξ)
    (σ : Fin 2) (z : CVec),
    helicalSymbol σ ξ z =
      (inner ℂ (b σ.castSucc) z) • b σ.castSucc :=
  @helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (b : OrthonormalBasis (Fin 3) ℂ CVec)
    (hcurl : ∀ τ : Fin 2,
      Complex.I • complexCross ξ (b τ.castSucc) =
        ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc)
    (hlong : b 2 = (‖ξ‖ : ℂ)⁻¹ • complexify ξ)
    (σ : Fin 2) (z : CVec),
    ‖helicalSymbol σ ξ z‖ ^ 2 =
      ‖inner ℂ (b σ.castSucc) z‖ ^ 2 :=
  @norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (b : OrthonormalBasis (Fin 3) ℂ CVec)
    (hcurl : ∀ τ : Fin 2,
      Complex.I • complexCross ξ (b τ.castSucc) =
        ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc)
    (hlong : b 2 = (‖ξ‖ : ℂ)⁻¹ • complexify ξ)
    (σ : Fin 2) (v : Field),
    helicalPower σ v ξ =
      ‖inner ℂ (b σ.castSucc) (fourierVelocity v ξ)‖ ^ 2 :=
  @helicalPower_eq_inner_sq_of_orthonormal_curl_frame

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame"
#check @MethbokeAddon.FDSNR3.helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame"
#check @MethbokeAddon.FDSNR3.norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame"
#print axioms MethbokeAddon.FDSNR3.norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalPower_eq_inner_sq_of_orthonormal_curl_frame"
#check @MethbokeAddon.FDSNR3.helicalPower_eq_inner_sq_of_orthonormal_curl_frame
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalPower_eq_inner_sq_of_orthonormal_curl_frame"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalPower_eq_inner_sq_of_orthonormal_curl_frame"
#print axioms MethbokeAddon.FDSNR3.helicalPower_eq_inner_sq_of_orthonormal_curl_frame
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalPower_eq_inner_sq_of_orthonormal_curl_frame"

