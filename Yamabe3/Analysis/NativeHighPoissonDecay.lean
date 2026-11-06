import Yamabe3.Analysis.NativeHighPoissonCoefficient
import Yamabe3.Analysis.HalfEndScalarExponentialDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Frequency-sensitive estimates for the actual high Poisson field.
These are estimates of its genuine angular coefficients, not a newly
chosen field or a geometric trace identification. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem NativeHighPotential.curve_coefficient_decay
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) (t : ℝ) (ht : 0 ≤ t) :
    (inner ℝ (angularBasis i) (P.curve b t)) ^ 2 ≤
      Real.exp (-2 * Real.sqrt (angularEigenvalue i - 7/2) * t) *
        (inner ℝ (angularBasis i) (angularEmbedding b)) ^ 2 := by
  let U := P.curve b
  let D := P.curveDerivative b
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  have hUt := halfEnd_tendsto_zero_of_expTwo_bound U (‖b‖ / (1-P.κ))
    (fun s hs => (nativeHalfHighPotentialPhysical_weighted_cauchy P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b s hs).1)
  have hDt := halfEnd_tendsto_zero_of_expTwo_bound D
    ((1+(10/9:ℝ)*‖P.potential‖/(1-P.κ))*‖b‖)
    (fun s hs => (nativeHalfHighPotentialPhysical_weighted_cauchy P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b s hs).2)
  have hz0 : ev (U 0) = inner ℝ (angularBasis i) (angularEmbedding b) := by
    change inner ℝ (angularBasis i) (P.curve b 0) = _
    rw [NativeHighPotential.curve, nativeHalfHighPotentialPhysical_zero,
      nativeHighEnergyProjectionCLM_embedding, nativeHighProjection,
      nativeAngularProjection_coefficient, if_pos hi]
  have h := halfEnd_scalar_exponential_square_bound (fun s => ev (U s))
    (fun s => ev (D s)) (fun s => nativeAngularRate i ^ 2 - P.potential s)
    (fun s hs => ev.hasFDerivAt.comp_hasDerivWithinAt s
      (nativeHalfHighPotentialPhysical_hasDerivWithinAt P.κ_nonneg P.κ_lt_one
        P.potential P.kernel_bound P.nonneg b s hs))
    (ev.continuous.comp (nativeHalfHighPotentialPhysicalDerivative_continuous
      P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b)).continuousOn
    (continuous_const.sub P.potential.continuous).continuousOn
    (nativeHalfHighPotentialPhysical_derivative_equation P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b i)
    (Real.sqrt (angularEigenvalue i - 7/2)) (fun s hs => by
      rw [highMode_coercivity_gap_sq _ hi, nativeAngularRate_sq, max_eq_right hi]
      linarith only [P.upper s hs])
    (by simpa only [Function.comp_def, map_zero] using ev.continuous.continuousAt.tendsto.comp hUt)
    (by simpa only [Function.comp_def, map_zero] using ev.continuous.continuousAt.tendsto.comp hDt)
    t ht
  rw [hz0] at h
  exact h

theorem NativeHighPotential.curve_coefficient_weight_decay
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (t : ℝ) (ht : 0 ≤ t) :
    (inner ℝ (angularBasis i) (P.curve b t)) ^ 2 ≤
      Real.exp (-(angularEnergyWeight i / 2) * t) *
        (inner ℝ (angularBasis i) (angularEmbedding b)) ^ 2 := by
  by_cases hi : 6 ≤ angularEigenvalue i
  · apply (P.curve_coefficient_decay b i hi t ht).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have h := highMode_coercivity_gap_lower (angularEigenvalue i) hi
    change angularEnergyWeight i / 4 ≤ Real.sqrt (angularEigenvalue i - 7/2) - 1/2 at h
    exact mul_le_mul_of_nonneg_right (by linarith) ht
  · rw [P.curve_low_zero b i (lt_of_not_ge hi) t, zero_pow (by decide)]
    positivity

/-- Actual time integral; the half power in the boundary norm comes
from integrating the rate-dependent exponential. -/
theorem NativeHighPotential.curve_coefficient_square_integral
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    IntegrableOn (fun t : ℝ => (inner ℝ (angularBasis i) (P.curve b t)) ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (inner ℝ (angularBasis i) (P.curve b t)) ^ 2) ≤
        (2 / angularEnergyWeight i) * (inner ℝ (angularBasis i) (angularEmbedding b)) ^ 2 := by
  let C := (inner ℝ (angularBasis i) (angularEmbedding b)) ^ 2
  have ha : -(angularEnergyWeight i / 2) < 0 := by
    have h := angularEnergyWeight_pos i
    linarith
  have hbound := (integrableOn_exp_mul_Ioi ha 0).mul_const C
  have hc : Continuous (fun t : ℝ => (inner ℝ (angularBasis i) (P.curve b t)) ^ 2) := by
    apply Continuous.pow
    apply (innerSL ℝ (angularBasis i)).continuous.comp
    change Continuous (fun t : ℝ => Real.exp (-2*t) •
      nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential
        P.kernel_bound P.nonneg b t.toNNReal)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential
        P.kernel_bound P.nonneg b).continuous.comp (by fun_prop))
  have hint : IntegrableOn
      (fun t : ℝ => (inner ℝ (angularBasis i) (P.curve b t)) ^ 2) (Ioi 0) := by
    apply hbound.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact P.curve_coefficient_weight_decay b i t ht.le
  refine ⟨hint, ?_⟩
  have hle := integral_mono_ae hint hbound (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact P.curve_coefficient_weight_decay b i t ht.le)
  rw [integral_mul_const, integral_exp_mul_Ioi ha 0] at hle
  norm_num only [mul_zero, Real.exp_zero] at hle
  have he : -1 / -(angularEnergyWeight i / 2) = 2 / angularEnergyWeight i := by
    field_simp [(angularEnergyWeight_pos i).ne']
    <;> ring
  simpa only [he, C] using hle

#print axioms NativeHighPotential.curve_coefficient_decay
#print axioms NativeHighPotential.curve_coefficient_weight_decay
#print axioms NativeHighPotential.curve_coefficient_square_integral
end Yamabe3.Analysis.Delaunay
