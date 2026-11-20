import FDSNResidualForce.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set SingularClosure
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff Topology

/- residualForce: literal physical definition. -/
example (ν : ℝ) (U F h : Velocity) (t : ℝ) (x : Vec) :
    MethbokeAddon.FDSN.residualForce ν U F h t x =
      F t x + timeDerivative h t x - ν • laplacian (h t) x +
        physicalTransport (U t) (h t) x +
        physicalTransport (h t) (U t) x + convection (h t) x := rfl

/- native_coordinateDerivative_contDiff. -/
example (a : Field) (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : Vec => fderiv ℝ a x (unitVector i)) :=
  MethbokeAddon.FDSN.native_coordinateDerivative_contDiff a ha i

/- native_coordinateDerivative_add. -/
example (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (i : Fin 3) :
    coordinateDerivative (a + b) i =
      coordinateDerivative a i + coordinateDerivative b i :=
  MethbokeAddon.FDSN.native_coordinateDerivative_add a b ha hb i

/- native_laplacian_add. -/
example (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    laplacian (a + b) = laplacian a + laplacian b :=
  MethbokeAddon.FDSN.native_laplacian_add a b ha hb

/- native_divergence_add. -/
example (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (x : Vec) :
    divergence (a + b) x = divergence a x + divergence b x :=
  MethbokeAddon.FDSN.native_divergence_add a b ha hb x

/- native_timeDerivative_add: one-sided convention expanded. -/
example (U h : Velocity) (t : ℝ) (x : Vec)
    (hU : DifferentiableWithinAt ℝ (fun r => U r x) (Ici (0 : ℝ)) t)
    (hh : DifferentiableWithinAt ℝ (fun r => h r x) (Ici (0 : ℝ)) t) :
    derivWithin (fun r : ℝ => (U + h) r x) (Ici (0 : ℝ)) t =
      derivWithin (fun r : ℝ => U r x) (Ici (0 : ℝ)) t +
      derivWithin (fun r : ℝ => h r x) (Ici (0 : ℝ)) t :=
  MethbokeAddon.FDSN.native_timeDerivative_add U h t x hU hh

/- native_residual_momentum_at: residualForce fully expanded. -/
example (ν : ℝ) (U F h : Velocity) (p : Pressure) (t : ℝ) (x : Vec)
    (hU : ContDiff ℝ ∞ (U t)) (hh : ContDiff ℝ ∞ (h t))
    (hUt : DifferentiableWithinAt ℝ (fun r => U r x) (Ici (0 : ℝ)) t)
    (hht : DifferentiableWithinAt ℝ (fun r => h r x) (Ici (0 : ℝ)) t)
    (hNSE : timeDerivative U t x + convection (U t) x +
        SingularClosure.gradient (p t) x =
      ν • laplacian (U t) x + F t x) :
    timeDerivative (U + h) t x + convection ((U + h) t) x +
        SingularClosure.gradient (p t) x =
      ν • laplacian ((U + h) t) x +
        (F t x + timeDerivative h t x - ν • laplacian (h t) x +
          physicalTransport (U t) (h t) x +
          physicalTransport (h t) (U t) x + convection (h t) x) :=
  MethbokeAddon.FDSN.native_residual_momentum_at ν U F h p t x hU hh hUt hht hNSE

/- native_divergence_add_zero. -/
example (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hda : ∀ x : Vec, divergence a x = 0)
    (hdb : ∀ x : Vec, divergence b x = 0) :
    ∀ x : Vec, divergence (a + b) x = 0 :=
  MethbokeAddon.FDSN.native_divergence_add_zero a b ha hb hda hdb

/- native_residual_momentum_on_open_slab: full literal slab equation. -/
example (ν : ℝ) (U F h : Velocity) (p : Pressure) (s T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2)
      {z | z.1 ∈ Ioo s T})
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2)
      {z | z.1 ∈ Ioo s T})
    (hNSE : ∀ t ∈ Ioo s T, ∀ x : Vec,
      timeDerivative U t x + convection (U t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (U t) x + F t x) :
    ∀ t ∈ Ioo s T, ∀ x : Vec,
      timeDerivative (U + h) t x + convection ((U + h) t) x +
          SingularClosure.gradient (p t) x =
        ν • laplacian ((U + h) t) x +
          (F t x + timeDerivative h t x - ν • laplacian (h t) x +
            physicalTransport (U t) (h t) x +
            physicalTransport (h t) (U t) x + convection (h t) x) :=
  MethbokeAddon.FDSN.native_residual_momentum_on_open_slab ν U F h p s T hU hh hNSE


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce"
#check @MethbokeAddon.FDSN.residualForce
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce"
#print axioms MethbokeAddon.FDSN.residualForce
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_coordinateDerivative_contDiff"
#check @MethbokeAddon.FDSN.native_coordinateDerivative_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_coordinateDerivative_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_coordinateDerivative_contDiff"
#print axioms MethbokeAddon.FDSN.native_coordinateDerivative_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_coordinateDerivative_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_coordinateDerivative_add"
#check @MethbokeAddon.FDSN.native_coordinateDerivative_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_coordinateDerivative_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_coordinateDerivative_add"
#print axioms MethbokeAddon.FDSN.native_coordinateDerivative_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_coordinateDerivative_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_laplacian_add"
#check @MethbokeAddon.FDSN.native_laplacian_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_laplacian_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_laplacian_add"
#print axioms MethbokeAddon.FDSN.native_laplacian_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_laplacian_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_divergence_add"
#check @MethbokeAddon.FDSN.native_divergence_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_divergence_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_divergence_add"
#print axioms MethbokeAddon.FDSN.native_divergence_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_divergence_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_timeDerivative_add"
#check @MethbokeAddon.FDSN.native_timeDerivative_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_timeDerivative_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_timeDerivative_add"
#print axioms MethbokeAddon.FDSN.native_timeDerivative_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_timeDerivative_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_residual_momentum_at"
#check @MethbokeAddon.FDSN.native_residual_momentum_at
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_residual_momentum_at"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_residual_momentum_at"
#print axioms MethbokeAddon.FDSN.native_residual_momentum_at
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_residual_momentum_at"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_divergence_add_zero"
#check @MethbokeAddon.FDSN.native_divergence_add_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_divergence_add_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_divergence_add_zero"
#print axioms MethbokeAddon.FDSN.native_divergence_add_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_divergence_add_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.native_residual_momentum_on_open_slab"
#check @MethbokeAddon.FDSN.native_residual_momentum_on_open_slab
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.native_residual_momentum_on_open_slab"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.native_residual_momentum_on_open_slab"
#print axioms MethbokeAddon.FDSN.native_residual_momentum_on_open_slab
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.native_residual_momentum_on_open_slab"

