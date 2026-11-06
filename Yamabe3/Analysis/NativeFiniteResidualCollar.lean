import Yamabe3.Analysis.NativeFiniteCollarEnergy

/-! Physical collar control from the actual value and Laplacian residual
of a finite conjugated field. Only local exponential weights are used;
no global boundedness of the negative-time exponential is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_exp_window_integral_bound {h : ℝ → ℝ} (hh : Integrable h)
    (hn : ∀ t,0 ≤ h t) (a : ℝ) {A : ℝ} (ha : |a| ≤ A) :
    IntegrableOn (fun t => Real.exp (a*t)*h t) (Ioo (-1) 1) ∧
      (∫ t : ℝ in Ioo (-1) 1,Real.exp (a*t)*h t) ≤ Real.exp A*(∫ t : ℝ,h t) := by
  have hb : ∀ t ∈ Ioo (-1:ℝ) 1,Real.exp (a*t) ≤ Real.exp A := by
    intro t ht
    apply Real.exp_le_exp.mpr
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    calc
      a*t ≤ |a*t| := le_abs_self _
      _ = |a| * |t| := abs_mul _ _
      _ ≤ A*1 := mul_le_mul ha ht1 (abs_nonneg _) ((abs_nonneg a).trans ha)
      _ = A := mul_one _
  have hi : IntegrableOn (fun t => Real.exp (a*t)*h t) (Ioo (-1) 1) := by
    apply hh.integrableOn.bdd_mul (c := Real.exp A) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hb t ht
  refine ⟨hi,?_⟩
  have hle := integral_mono_ae hi (hh.integrableOn.const_mul (Real.exp A)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_le_mul_of_nonneg_right (hb t ht) (hn t))
  rw [integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hh (Eventually.of_forall hn)) (Real.exp_pos _).le)

theorem native_finite_conjugated_collar_energy (s : Finset AngularIndex)
    (U G : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s,ContDiff ℝ 2 (fun t => Real.exp (-2*t)*U i t))
    (hode : ∀ i ∈ s,∀ t,finiteTimeLaplacian (fun i t => Real.exp (-2*t)*U i t) i t=
      Real.exp (-2*t)*G i t)
    (hU : ∀ i ∈ s,Integrable (fun t => U i t^2))
    (hG : ∀ i ∈ s,Integrable (fun t => G i t^2)) :
    let u := finitePhysical s (fun i t => Real.exp (-2*t)*U i t)
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
      IntegrableOn (fun x => u x^2) O ∧
      IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        Real.exp 6*(∑ i ∈ s,∫ t : ℝ,U i t^2)+Real.exp 2*(∑ i ∈ s,∫ t : ℝ,G i t^2) := by
  let q := fun i t => Real.exp (-2*t)*U i t
  let u := finitePhysical s q
  have hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E) := finitePhysical_contDiffOn_offZero_C2 s q hq
  have hv := native_exp_window_integral_bound (integrable_finsetSum s hU)
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (U i t))) (-6) (by norm_num : |(-6:ℝ)|≤6)
  have hl := native_exp_window_integral_bound (integrable_finsetSum s hG)
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (G i t))) (-2) (by norm_num : |(-2:ℝ)|≤2)
  have hexp (a t : ℝ) : Real.exp (a*t)*Real.exp (-2*t)^2=Real.exp ((a-4)*t) := by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hval (t : ℝ) :
      (∫ θ : S,Real.exp (-3*t)*u (cylinderPoint (t,θ))^2 ∂angularVolume)=
        Real.exp (-6*t)*(∑ i ∈ s,U i t^2) := by
    rw [native_finitePhysical_value_log_square]
    dsimp [q]
    simp only [mul_pow,←Finset.mul_sum,←mul_assoc,hexp]
    norm_num
  have hlap (t : ℝ) :
      (∫ θ : S,Real.exp (-3*t)*nativeCoordinateLaplacian u (cylinderPoint (t,θ))^2 ∂angularVolume)=
        Real.exp (-2*t)*(∑ i ∈ s,G i t^2) := by
    rw [native_finitePhysical_laplacian_log_square s q hq]
    have he : (∑ i ∈ s,finiteTimeLaplacian q i t^2)=Real.exp (-2*t)^2*(∑ i ∈ s,G i t^2) := by
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
  simpa only [u,q,Pi.pow_apply,integral_finsetSum s hU,integral_finsetSum s hG] using h

#print axioms native_exp_window_integral_bound
#print axioms native_finite_conjugated_collar_energy
end Yamabe3.Analysis.SpherePolar
