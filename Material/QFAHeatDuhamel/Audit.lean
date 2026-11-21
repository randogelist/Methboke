import QFAHeatDuhamel.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatDuhamel
open scoped NNReal ENNReal Topology

noncomputable section

example (ν : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × SpatialL2 => heatL2 ν p.1 p.2) :=
  heatL2_joint_continuous ν

/- The public constructor is the literal retarded Bochner integral. -/
example (ν : ℝ≥0) (f : ℝ → SpatialL2) (t : ℝ) :
    duhamelL2 ν f t = ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s) := rfl

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (μ : Measure ℝ)
    (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    AEStronglyMeasurable (fun s : ℝ => heatL2 ν (t - s).toNNReal (f s)) μ :=
  duhamelL2_integrand_aestronglyMeasurable ν f μ hf t

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (htT : t ≤ T) :
    MemLp (fun s : ℝ => heatL2 ν (t - s).toNNReal (f s))
      2 (volume.restrict (Ioc (0 : ℝ) t)) :=
  duhamelL2_integrand_memLp_two ν f T hf t htT

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun s : ℝ => heatL2 ν (t - s).toNNReal (f s)) volume 0 t :=
  duhamelL2_integrand_intervalIntegrable ν f T hf t ht htT

example (ν : ℝ≥0) (f : ℝ → SpatialL2) :
    duhamelL2 ν f 0 = (0 : SpatialL2) :=
  duhamelL2_zero_time ν f

example (ν : ℝ≥0) (t : ℝ) :
    duhamelL2 ν (fun _ : ℝ => (0 : SpatialL2)) t = 0 :=
  duhamelL2_zero_forcing ν t

/- The a.e. premise concerns exactly the original physical time window. -/
example (ν : ℝ≥0) (f g : ℝ → SpatialL2) (T : ℝ)
    (hfg : f =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] g)
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)) =
      ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (g s) :=
  duhamelL2_ae_eq ν f g T hfg t ht htT

example (ν : ℝ≥0) (f g : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s + g s)) =
      (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)) +
      (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (g s)) :=
  duhamelL2_add ν f g T hf hg t ht htT

example (ν : ℝ≥0) (c : ℝ) (f : ℝ → SpatialL2) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (c • f s)) =
      c • (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)) :=
  duhamelL2_smul ν c f t

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)‖ ≤
      ∫ s in (0 : ℝ)..t, ‖f s‖ :=
  duhamelL2_norm_le_integral_norm ν f T hf t ht htT

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)‖ ≤
      Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) :=
  duhamelL2_norm_le_sqrt_mul ν f T hf t ht htT

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)‖ ≤
      Real.sqrt T * Real.sqrt (∫ s in (0 : ℝ)..T, ‖f s‖ ^ 2) :=
  duhamelL2_norm_le_sqrt_horizon ν f T hf t ht htT

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)‖ ≤
      Real.sqrt T * ‖hf.toLp f‖ :=
  duhamelL2_norm_le_sqrt_mul_lpNorm ν f T hf t ht htT

example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ) (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ContinuousOn (fun t : ℝ =>
      ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)) (Icc (0 : ℝ) T) :=
  duhamelL2_continuousOn ν f T hT hf

/- One common actual path carries the trace, integral and uniform bound. -/
example (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ) (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ∃ w : ℝ → SpatialL2,
      ContinuousOn w (Icc (0 : ℝ) T) ∧ w 0 = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        w t = (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)) ∧
        ‖w t‖ ≤ Real.sqrt T * ‖hf.toLp f‖ := by
  refine ⟨duhamelL2 ν f, duhamelL2_continuousOn ν f T hT hf,
    duhamelL2_zero_time ν f, ?_⟩
  intro t ht
  exact ⟨rfl, duhamelL2_norm_le_sqrt_mul_lpNorm ν f T hf t ht.1 ht.2⟩

/- No artificial strictly positive-viscosity premise is introduced into
this low-frequency response: at zero viscosity it is the actual primitive. -/
example (f : ℝ → SpatialL2) (t : ℝ) :
    duhamelL2 0 f t = ∫ s in (0 : ℝ)..t, f s := by
  simp only [duhamelL2, heatL2_zero_viscosity]

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.heatL2_joint_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.heatL2_joint_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.heatL2_joint_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.heatL2_joint_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.heatL2_joint_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.heatL2_joint_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_aestronglyMeasurable"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_aestronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_aestronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_aestronglyMeasurable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_aestronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_aestronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_memLp_two"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_memLp_two
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_memLp_two"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_memLp_two"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_memLp_two
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_memLp_two"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_intervalIntegrable"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_intervalIntegrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_intervalIntegrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_intervalIntegrable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_intervalIntegrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_integrand_intervalIntegrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_forcing"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_forcing
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_forcing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_forcing"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_forcing
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_zero_forcing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_add"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_add"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_smul"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_integral_norm"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_integral_norm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_integral_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_integral_norm"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_integral_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_integral_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_horizon"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_horizon
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_horizon"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_horizon"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_horizon
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_horizon"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn"

