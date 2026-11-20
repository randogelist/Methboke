import FDSNPhysicalPair.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory
open scoped BigOperators ContDiff
open SingularClosure MethbokeAddon.FDSN

noncomputable section

example {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hd : ∀ x : Vec, divergence v x = 0) :
    SpectralSolenoidal (datumFourierCoeff v) :=
  smoothPeriodic_fourier_solenoidal hv hp hd
example {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    RapidScalarFourier (fun k => datumFourierCoeff v k i) :=
  smoothPeriodic_fourier_rapid hv hp i
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1) {c : FourierCoeff}
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i)) (i : Fin 3) :
    RapidScalarFourier (fun k => pairRotate a z c k i) := pairRotate_rapid a hz hc i
example {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    smoothFourierSynthesis (datumFourierCoeff v) = v :=
  smoothPeriodic_fourier_reconstruction hv hp
example : Frequency → ℂ → Field → Field := physicalPairRotation
example (a : Frequency) (z : ℂ) (v : Field) :
    physicalPairRotation a z v =
      smoothFourierSynthesis (pairRotate a z (datumFourierCoeff v)) := rfl
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    ContDiff ℝ ∞ (physicalPairRotation a z v) := physicalPairRotation_smooth a hz hv hp
example (a : Frequency) (z : ℂ) (v : Field) :
    SpatialPeriodic (physicalPairRotation a z v) := physicalPairRotation_periodic a z v
example {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalPairRotation a z v) =
      pairRotate a z (datumFourierCoeff v) := physicalPairRotation_coeff ha hz hv hp
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hd : ∀ x : Vec, divergence v x = 0) :
    ∀ x : Vec, divergence (physicalPairRotation a z v) x = 0 :=
  physicalPairRotation_divergence_free a hz hv hp hd
example (a : Frequency) {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalPairRotation a 1 v = v := physicalPairRotation_one a hv hp
example {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalPairRotation a z v) 0 = datumFourierCoeff v 0 :=
  physicalPairRotation_mean_coeff ha hz hv hp
example {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    spatialMean (physicalPairRotation a z v) = spatialMean v :=
  physicalPairRotation_mean ha hz hv hp
example {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (k : Frequency) (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) :
    ‖L (datumFourierCoeff (physicalPairRotation a z v) k)‖ =
      ‖L (datumFourierCoeff v k)‖ := physicalPairRotation_observable_norm ha hz hv hp k L
example {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1)
    {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hd : ∀ x : Vec, divergence v x = 0) :
    ContDiff ℝ ∞ (physicalPairRotation a z v) ∧
    SpatialPeriodic (physicalPairRotation a z v) ∧
    (∀ x : Vec, divergence (physicalPairRotation a z v) x = 0) ∧
    spatialMean (physicalPairRotation a z v) = spatialMean v ∧
    (∀ k : Frequency, ∀ L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ,
      ‖L (datumFourierCoeff (physicalPairRotation a z v) k)‖ =
        ‖L (datumFourierCoeff v k)‖) :=
  PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA ha hz hv hp hd


end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_fourier_solenoidal"
#check @MethbokeAddon.FDSN.smoothPeriodic_fourier_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smoothPeriodic_fourier_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_fourier_solenoidal"
#print axioms MethbokeAddon.FDSN.smoothPeriodic_fourier_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smoothPeriodic_fourier_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_fourier_rapid"
#check @MethbokeAddon.FDSN.smoothPeriodic_fourier_rapid
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smoothPeriodic_fourier_rapid"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_fourier_rapid"
#print axioms MethbokeAddon.FDSN.smoothPeriodic_fourier_rapid
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smoothPeriodic_fourier_rapid"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_rapid"
#check @MethbokeAddon.FDSN.pairRotate_rapid
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_rapid"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_rapid"
#print axioms MethbokeAddon.FDSN.pairRotate_rapid
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_rapid"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_fourier_reconstruction"
#check @MethbokeAddon.FDSN.smoothPeriodic_fourier_reconstruction
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smoothPeriodic_fourier_reconstruction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_fourier_reconstruction"
#print axioms MethbokeAddon.FDSN.smoothPeriodic_fourier_reconstruction
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smoothPeriodic_fourier_reconstruction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation"
#check @MethbokeAddon.FDSN.physicalPairRotation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation"
#print axioms MethbokeAddon.FDSN.physicalPairRotation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_smooth"
#check @MethbokeAddon.FDSN.physicalPairRotation_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_smooth"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_periodic"
#check @MethbokeAddon.FDSN.physicalPairRotation_periodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_periodic"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_coeff"
#check @MethbokeAddon.FDSN.physicalPairRotation_coeff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_coeff"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_divergence_free"
#check @MethbokeAddon.FDSN.physicalPairRotation_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_divergence_free"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_one"
#check @MethbokeAddon.FDSN.physicalPairRotation_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_one"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_mean_coeff"
#check @MethbokeAddon.FDSN.physicalPairRotation_mean_coeff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_mean_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_mean_coeff"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_mean_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_mean_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_mean"
#check @MethbokeAddon.FDSN.physicalPairRotation_mean
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_mean"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_mean"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_mean
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_mean"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_observable_norm"
#check @MethbokeAddon.FDSN.physicalPairRotation_observable_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_observable_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_observable_norm"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_observable_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_observable_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA"
#check @MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA"
#print axioms MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA"

