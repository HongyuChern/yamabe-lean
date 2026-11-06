import Yamabe3.Analysis.NativeHighForcedBoundaryMatching
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Public actual-coordinate regularity and true-eigenvalue equations
for the exact Poisson curve used in the coupled boundary construction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

private theorem poisson_coordinate (P:NativeHighPotential) (b:AngularH1) (i:AngularIndex) (t:ℝ):
    inner ℝ (angularBasis i) (P.curve b t)=
      Real.exp (-2*t)*spectralHalfPotentialPoissonCLM nativeAngularRate (by norm_num)
        nativeAngularRate_lower P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg
        (angularBasis.repr (nativeHighProjection (angularEmbedding b))) t.toNNReal i:=by
  rw [NativeHighPotential.curve,nativeHalfHighPotentialPhysical,real_inner_smul_right,
    nativeHalfHighPotentialPoissonCLM_apply,←HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem NativeHighPotential.curve_low_zero (P:NativeHighPotential) (b:AngularH1)
    (i:AngularIndex) (hi:angularEigenvalue i<6) (t:ℝ):
    inner ℝ (angularBasis i) (P.curve b t)=0:=by
  rw [poisson_coordinate,spectralHalfPotentialPoissonCLM_coordinate_zero,mul_zero]
  rw [HilbertBasis.repr_apply_apply,nativeHighProjection,nativeAngularProjection_coefficient,
    if_neg (not_le.mpr hi)]

theorem NativeHighPotential.curve_coefficient_C2 (P:NativeHighPotential) (b:AngularH1)
    (i:AngularIndex):ContDiffOn ℝ 2 (fun t=>inner ℝ (angularBasis i) (P.curve b t)) (Ioi 0):=by
  simp_rw [poisson_coordinate]
  exact spectralHalfPotentialPoissonCLM_physical_coordinate_c2 nativeAngularRate (by norm_num)
    nativeAngularRate_lower P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg _ i

theorem NativeHighPotential.curve_coefficient_equation (P:NativeHighPotential) (b:AngularH1)
    (i:AngularIndex) (t:ℝ) (ht:0<t):
    deriv (deriv (fun s=>inner ℝ (angularBasis i) (P.curve b s))) t=
      (angularEigenvalue i+1/4-P.potential t)*inner ℝ (angularBasis i) (P.curve b t):=by
  have h:=spectralHalfPotentialPoissonCLM_physical_coordinate_equation nativeAngularRate (by norm_num)
    nativeAngularRate_lower P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg
    (angularBasis.repr (nativeHighProjection (angularEmbedding b))) i t ht
  have he:deriv (deriv (fun s=>inner ℝ (angularBasis i) (P.curve b s))) t=
      (nativeAngularRate i^2-P.potential t)*inner ℝ (angularBasis i) (P.curve b t):=by
    simp_rw [poisson_coordinate]
    exact h.deriv
  by_cases hi:6≤angularEigenvalue i
  · rw [nativeAngularRate_sq,max_eq_right hi] at he
    exact he
  · rw [P.curve_low_zero b i (lt_of_not_ge hi) t,mul_zero] at he ⊢
    exact he

theorem bubbleExteriorPoisson_coefficient_equation (t₀:ℝ) (b:AngularH1)
    (i:AngularIndex) (t:ℝ) (ht:t<0):
    deriv (deriv (fun s=>inner ℝ (angularBasis i) ((fullBubbleHighPotential (-t₀)).curve b (-s)))) t=
      (angularEigenvalue i+1/4-(15/4)*fullBubbleDensity (t₀+t))*
        inner ℝ (angularBasis i) ((fullBubbleHighPotential (-t₀)).curve b (-t)):=by
  let B:=fullBubbleHighPotential (-t₀)
  let u:=fun s=>inner ℝ (angularBasis i) (B.curve b s)
  have hd:deriv (fun s=>u (-s))=fun s=> -deriv u (-s):=funext fun s=>deriv_comp_neg u s
  change deriv (deriv (fun s=>u (-s))) t=_
  rw [hd]
  change deriv (-(fun s=>deriv u (-s))) t=_
  rw [deriv.neg,deriv_comp_neg,neg_neg,B.curve_coefficient_equation b i (-t) (neg_pos.mpr ht)]
  rw [fullBubble_exterior_potential]
  simp only [sub_neg_eq_add,B]

#print axioms NativeHighPotential.curve_low_zero
#print axioms NativeHighPotential.curve_coefficient_C2
#print axioms NativeHighPotential.curve_coefficient_equation
#print axioms bubbleExteriorPoisson_coefficient_equation
end Yamabe3.Analysis.Delaunay
