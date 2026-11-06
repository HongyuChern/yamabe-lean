import Yamabe3.Analysis.NativeFiniteResidualCollar

/-! Reverse-time physical collar estimates retain the actual exponential
weights. Whole-line L2 reflection is measure preserving; no endpoint or
source regularity is silently strengthened. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_finite_reverse_conjugated_collar_energy (s : Finset AngularIndex)
    (U G : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s,ContDiff ℝ 2 (fun t => Real.exp (2*t)*U i (-t)))
    (hode : ∀ i ∈ s,∀ t,finiteTimeLaplacian (fun i t => Real.exp (2*t)*U i (-t)) i t=
      Real.exp (2*t)*G i (-t))
    (hU : ∀ i ∈ s,Integrable (fun t => U i t^2))
    (hG : ∀ i ∈ s,Integrable (fun t => G i t^2)) :
    let u := finitePhysical s (fun i t => Real.exp (2*t)*U i (-t))
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
      IntegrableOn (fun x => u x^2) O ∧
      IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        Real.exp 2*(∑ i ∈ s,∫ t : ℝ,U i t^2)+Real.exp 6*(∑ i ∈ s,∫ t : ℝ,G i t^2) := by
  let q := fun i t => Real.exp (2*t)*U i (-t)
  let u := finitePhysical s q
  have hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E) := finitePhysical_contDiffOn_offZero_C2 s q hq
  have hUr (i : AngularIndex) (hi : i∈s) : Integrable (fun t => U i (-t)^2) := (hU i hi).comp_neg
  have hGr (i : AngularIndex) (hi : i∈s) : Integrable (fun t => G i (-t)^2) := (hG i hi).comp_neg
  have hv := native_exp_window_integral_bound (integrable_finsetSum s hUr)
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (U i (-t)))) 2 (by norm_num : |(2:ℝ)|≤2)
  have hl := native_exp_window_integral_bound (integrable_finsetSum s hGr)
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (G i (-t)))) 6 (by norm_num : |(6:ℝ)|≤6)
  have hexp (a t : ℝ) : Real.exp (a*t)*Real.exp (2*t)^2=Real.exp ((a+4)*t) := by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hval (t : ℝ) :
      (∫ θ : S,Real.exp (-3*t)*u (cylinderPoint (t,θ))^2 ∂angularVolume)=
        Real.exp (2*t)*(∑ i ∈ s,U i (-t)^2) := by
    rw [native_finitePhysical_value_log_square]
    dsimp [q]
    simp only [mul_pow,←Finset.mul_sum,←mul_assoc,hexp]
    norm_num
  have hlap (t : ℝ) :
      (∫ θ : S,Real.exp (-3*t)*nativeCoordinateLaplacian u (cylinderPoint (t,θ))^2 ∂angularVolume)=
        Real.exp (6*t)*(∑ i ∈ s,G i (-t)^2) := by
    rw [native_finitePhysical_laplacian_log_square s q hq]
    have he : (∑ i ∈ s,finiteTimeLaplacian q i t^2)=Real.exp (2*t)^2*(∑ i ∈ s,G i (-t)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hode i hi t,mul_pow]
    rw [he,←mul_assoc,hexp]
    norm_num
  have hvp := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    ((hu.continuousOn.pow 2).mono (fun x hx => hx.1)) (fun _ _ => sq_nonneg _) hv.1
    (fun t _ => hval t)
  have hlp := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    (((continuousOn_nativeCoordinateLaplacian isClosed_singleton.isOpen_compl hu).pow 2).mono
      (fun x hx => hx.1)) (fun _ _ => sq_nonneg _) hl.1 (fun t _ => hlap t)
  refine ⟨hu,hvp.1,hlp.1,?_⟩
  have h := add_le_add (hvp.2.trans_le hv.2) (hlp.2.trans_le hl.2)
  have heU (i : AngularIndex) : (∫t : ℝ,U i (-t)^2)=(∫t : ℝ,U i t^2) :=
    integral_neg_eq_self (fun t => U i t^2) volume
  have heG (i : AngularIndex) : (∫t : ℝ,G i (-t)^2)=(∫t : ℝ,G i t^2) :=
    integral_neg_eq_self (fun t => G i t^2) volume
  simpa only [u,q,Pi.pow_apply,integral_finsetSum s hUr,integral_finsetSum s hGr,heU,heG] using h

#print axioms native_finite_reverse_conjugated_collar_energy
end Yamabe3.Analysis.SpherePolar
