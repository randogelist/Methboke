import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import QuasiFeffermanB.GoodTime
import QuasiFeffermanB.LHRestart
import QuasiFeffermanB.Endpoints.Root

/-!
Passive anchor check preparation. NOT EXECUTED.
Native Material / frozen fdb515d8 environment; Lean4.33.0 and Mathlib db584cd6.
Only a later authorized external cached environment may execute this file.
No new theorem or analytic witness is defined. Full theorem parameters remain material.
- Research source inspection does not establish A-tier.
-/

set_option pp.all true
set_option pp.universes true

#check @MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner
#print axioms MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner

#check @MeasureTheory.Lp.norm_fourier_eq
#print axioms MeasureTheory.Lp.norm_fourier_eq

#check @SchwartzMap.fourier_lineDerivOp_eq
#print axioms SchwartzMap.fourier_lineDerivOp_eq

#check @SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
#print axioms SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left

#check @SchwartzMap.integral_bilinear_laplacian_right_eq_left
#print axioms SchwartzMap.integral_bilinear_laplacian_right_eq_left

#check @IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
#print axioms IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral

#check @IntervalIntegrable.ae_hasDerivAt_integral
#print axioms IntervalIntegrable.ae_hasDerivAt_integral

#check @AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
#print axioms AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub

#check @MeasureTheory.mul_meas_ge_le_integral_of_nonneg
#print axioms MeasureTheory.mul_meas_ge_le_integral_of_nonneg

#check @QuasiFeffermanB.exists_good_time_of_integral_lt
#print axioms QuasiFeffermanB.exists_good_time_of_integral_lt

#check @QuasiFeffermanB.strong_tendsto_of_inner_and_norm_bound
#print axioms QuasiFeffermanB.strong_tendsto_of_inner_and_norm_bound

#check @QuasiFeffermanB.LH_RESTART_AE_Ioo
#print axioms QuasiFeffermanB.LH_RESTART_AE_Ioo

#check @QuasiFeffermanB.LH_TAIL_ENERGY_OF_POSITIVE_FLOW
#print axioms QuasiFeffermanB.LH_TAIL_ENERGY_OF_POSITIVE_FLOW

#check @QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_SMOOTH_FLOW
#print axioms QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_SMOOTH_FLOW

#check @QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
#print axioms QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED
