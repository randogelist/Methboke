import R0PressureUniqueness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae
example : ∀ {u v : Field} (hu : Continuous u) (hv : Continuous v)
    (huper : SpatialPeriodic u) (hvper : SpatialPeriodic v)
    (hae : u =ᵐ[volume.restrict unitCube] v),
    u = v :=
  @MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const
example : ∀ (c : ℝ),
    (∫ _x : Vec in unitCube, c) = c :=
  @MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq
example : ∀ {p q : Vec → ℝ} {x : Vec} (hgrad : SingularClosure.gradient p x = SingularClosure.gradient q x),
    fderiv ℝ p x = fderiv ℝ q x :=
  @MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq
example : ∀ {p q : Vec → ℝ}
    (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hpmean : PressureMeanZero p) (hqmean : PressureMeanZero q)
    (hgrad : ∀ x : Vec, SingularClosure.gradient p x = SingularClosure.gradient q x),
    p = q :=
  @MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap
example : ∀ {u v : Velocity} {I : Set ℝ} (hI : IsOpen I)
    (hvel : ∀ t ∈ I, u t = v t) {t : ℝ} (ht : t ∈ I) (x : Vec),
    timeDerivative u t x = timeDerivative v t x :=
  @MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap
example : ∀ {ν : ℝ} {u v : Velocity} {p q : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hvel : ∀ t ∈ I, u t = v t)
    (hu : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (u t) x)
    (hv : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
        ν • laplacian (v t) x),
    ∀ t ∈ I, SingularClosure.gradient (p t) = SingularClosure.gradient (q t) :=
  @MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap
example : ∀ {ν : ℝ} {u v : Velocity} {p q : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hvel : ∀ t ∈ I, u t = v t)
    (hu : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (u t) x)
    (hv : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
        ν • laplacian (v t) x)
    (hp : ∀ t ∈ I, ContDiff ℝ ∞ (p t))
    (hq : ∀ t ∈ I, ContDiff ℝ ∞ (q t))
    (hpmean : ∀ t ∈ I, PressureMeanZero (p t))
    (hqmean : ∀ t ∈ I, PressureMeanZero (q t)),
    ∀ t ∈ I, p t = q t :=
  @MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set
example : ∀ {p : Pressure} {I : Set ℝ} (hI : IsOpen I)
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I}) {t : ℝ} (ht : t ∈ I),
    ContDiff ℝ ∞ (p t) :=
  @MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap
example : ∀ {ν : ℝ} {u v : Velocity} {p q : Pressure} {I : Set ℝ}
    (hI : IsOpen I) (hvel : ∀ t ∈ I, u t = v t)
    (hu : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
        ν • laplacian (u t) x)
    (hv : ∀ t ∈ I, ∀ x : Vec,
      timeDerivative v t x + convection (v t) x + SingularClosure.gradient (q t) x =
        ν • laplacian (v t) x)
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I})
    (hq : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => q z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I})
    (hpmean : ∀ t ∈ I, PressureMeanZero (p t))
    (hqmean : ∀ t ∈ I, PressureMeanZero (q t)),
    ∀ t ∈ I, p t = q t :=
  @MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae"
#check @MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae"
#print axioms MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.continuous_periodic_field_eq_of_cube_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const"
#check @MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const"
#print axioms MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.pressure_integral_unitCube_const"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq"
#check @MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq"
#print axioms MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.scalar_fderiv_eq_of_gradient_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq"
#check @MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq"
#print axioms MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap"
#check @MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap"
#print axioms MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.timeDerivative_eq_on_open_velocity_overlap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap"
#check @MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap"
#print axioms MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.pressure_gradient_eq_on_open_velocity_overlap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap"
#check @MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap"
#print axioms MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_open_velocity_overlap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set"
#check @MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set"
#print axioms MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.pressure_slice_contDiff_on_open_time_set"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap"
#check @MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap"
#print axioms MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_on_jointly_smooth_velocity_overlap"

