import Yamabe3.Analysis.NativeHighPoissonDecay
import Yamabe3.Analysis.HalfEndScalarEnergyIntegral

/-! The genuine Poisson derivative has an integrable square, with its
energy bounded by the actual DtN symbol. The symbol upper bound follows
from the previously proved operator estimate on a real energy mode. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem native_angularEnergyMode_norm (i : AngularIndex) :
    ‖angularEnergyMode i‖ = angularEnergyWeight i := by
  have h := angularEnergyMode_inner i (angularEnergyMode i)
  rw [real_inner_self_eq_norm_sq, angularEmbedding_energyMode,
    real_inner_self_eq_norm_sq, angularBasis.orthonormal.1, one_pow, mul_one] at h
  have hw := angularEnergyWeight_sq i
  have hp := angularEnergyWeight_pos i
  nlinarith only [h, hw, hp, norm_nonneg (angularEnergyMode i)]

def NativeHighPotential.derivativeBound (P : NativeHighPotential) : ℝ :=
  1 + (10/9:ℝ)*‖P.potential‖/(1-P.κ)

theorem NativeHighPotential.symbol_upper (P : NativeHighPotential) (i : AngularIndex) :
    P.symbol i ≤ P.derivativeBound * angularEnergyWeight i := by
  have hd := (nativeHalfHighPotentialPhysical_weighted_cauchy P.κ_nonneg P.κ_lt_one
    P.potential P.kernel_bound P.nonneg (angularEnergyMode i) 0 le_rfl).2
  simp only [mul_zero, Real.exp_zero, one_mul, native_angularEnergyMode_norm] at hd
  change inner ℝ (angularBasis i) (-nativeHalfHighPotentialPhysicalDerivative
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg (angularEnergyMode i) 0) ≤ _
  apply (real_inner_le_norm _ _).trans
  simpa only [angularBasis.orthonormal.1, norm_neg, one_mul, NativeHighPotential.derivativeBound] using hd

theorem NativeHighPotential.curve_derivative_square_integral
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) :
    IntegrableOn (fun t : ℝ => (inner ℝ (angularBasis i) (P.curveDerivative b t)) ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (inner ℝ (angularBasis i) (P.curveDerivative b t)) ^ 2) ≤
        P.derivativeBound * angularEnergyWeight i *
          (inner ℝ (angularBasis i) (angularEmbedding b)) ^ 2 := by
  let U := P.curve b
  let D := P.curveDerivative b
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  have hUt := halfEnd_tendsto_zero_of_expTwo_bound U (‖b‖/(1-P.κ))
    (fun t ht => (nativeHalfHighPotentialPhysical_weighted_cauchy P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b t ht).1)
  have hDt := halfEnd_tendsto_zero_of_expTwo_bound D (P.derivativeBound*‖b‖)
    (fun t ht => (nativeHalfHighPotentialPhysical_weighted_cauchy P.κ_nonneg P.κ_lt_one
      P.potential P.kernel_bound P.nonneg b t ht).2)
  have h := halfEnd_scalar_derivative_square_integral (fun t => ev (U t))
    (fun t => ev (D t)) (fun t => nativeAngularRate i^2-P.potential t)
    (fun t ht => ev.hasFDerivAt.comp_hasDerivWithinAt t
      (nativeHalfHighPotentialPhysical_hasDerivWithinAt P.κ_nonneg P.κ_lt_one P.potential
        P.kernel_bound P.nonneg b t ht))
    (ev.continuous.comp (nativeHalfHighPotentialPhysicalDerivative_continuous
      P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b)).continuousOn
    (nativeHalfHighPotentialPhysical_derivative_equation P.κ_nonneg P.κ_lt_one P.potential
      P.kernel_bound P.nonneg b i)
    (fun t ht => by
      rw [nativeAngularRate_sq, max_eq_right hi]
      linarith only [hi, P.upper t ht])
    (by simpa only [Function.comp_def, map_zero] using ev.continuous.continuousAt.tendsto.comp hUt)
    (by simpa only [Function.comp_def, map_zero] using ev.continuous.continuousAt.tendsto.comp hDt)
  have hz0 : ev (U 0) = inner ℝ (angularBasis i) (angularEmbedding b) := by
    change inner ℝ (angularBasis i) (P.curve b 0) = _
    rw [NativeHighPotential.curve, nativeHalfHighPotentialPhysical_zero,
      nativeHighEnergyProjectionCLM_embedding, nativeHighProjection,
      nativeAngularProjection_coefficient, if_pos hi]
  have hd0 : -ev (D 0) = P.symbol i * inner ℝ (angularBasis i) (angularEmbedding b) := by
    change -inner ℝ (angularBasis i) (P.curveDerivative b 0) = _
    have h := P.coefficient b i
    rw [if_pos hi] at h
    change inner ℝ (angularBasis i) (-P.curveDerivative b 0) = _ at h
    simpa only [inner_neg_right] using h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [hz0, hd0, mul_assoc, ← pow_two]
  exact mul_le_mul_of_nonneg_right (P.symbol_upper i) (sq_nonneg _)

#print axioms native_angularEnergyMode_norm
#print axioms NativeHighPotential.symbol_upper
#print axioms NativeHighPotential.curve_derivative_square_integral
end Yamabe3.Analysis.Delaunay
