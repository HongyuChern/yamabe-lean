import Yamabe3.Analysis.NativeFiniteCollarEnergy

/-! Local time-window energy bounds. Unlike a whole-line L2 estimate,
these apply to the actual low Cauchy solutions on their negative half-end. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_exp_window_bound {h : ℝ→ℝ} (hh : Continuous h)
    (hn : ∀t,0≤h t) (B a : ℝ) (ha : |a|≤2)
    (hb : ∀t∈Ioo (-1:ℝ) 1,h t≤B) :
    IntegrableOn (fun t => Real.exp (a*t)*h t) (Ioo (-1) 1) ∧
      (∫t : ℝ in Ioo (-1) 1,Real.exp (a*t)*h t)≤2*Real.exp 2*B := by
  have hc : Continuous (fun t => Real.exp (a*t)*h t) := by fun_prop
  have hi : IntegrableOn (fun t => Real.exp (a*t)*h t) (Ioo (-1) 1) := hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine ⟨hi,?_⟩
  have hle := setIntegral_mono_on hi
    ((continuous_const : Continuous (fun _ : ℝ => Real.exp 2*B)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    measurableSet_Ioo (fun t ht => ?_)
  · norm_num [integral_const,Real.volume_Ioo] at hle
    simpa only [mul_assoc] using hle
  · have hex : Real.exp (a*t)≤Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      have ht1 : |t|≤1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
      calc
        a*t ≤ |a*t| := le_abs_self _
        _ = |a| * |t| := abs_mul _ _
        _ ≤ 2*1 := mul_le_mul ha ht1 (abs_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    exact mul_le_mul hex (hb t ht) (hn t) (Real.exp_pos _).le

theorem native_finitePhysical_window_energy (m : Finset AngularIndex)
    (q : AngularIndex→ℝ→ℝ) (hq : ∀i∈m,ContDiff ℝ 2 (q i))
    (A B : AngularIndex→ℝ) (hA : ∀i∈m,0≤A i) (hB : ∀i∈m,0≤B i)
    (h0 : ∀i∈m,∀t∈Ioo (-1:ℝ) 1,‖q i t‖≤A i)
    (h2 : ∀i∈m,∀t∈Ioo (-1:ℝ) 1,‖deriv (deriv (q i)) t‖≤B i) :
    let W := nativePolarTimeWindow (Ioo (-1) 1)
    (∫x in W,finitePhysical m q x^2)+(∫x in W,nativeCoordinateLaplacian (finitePhysical m q) x^2)≤
      2*Real.exp 2*(∑i∈m,((A i)^2+2*((B i)^2+angularEnergyWeight i^4*(A i)^2))) := by
  have hq2 (i : AngularIndex) (hi : i∈m) : Continuous (deriv (deriv (q i))) := by
    have hd : ContDiff ℝ 1 (deriv (q i)) := (contDiff_succ_iff_deriv.mp (hq i hi)).2.2
    exact hd.continuous_deriv (by norm_num)
  have hval := native_exp_window_bound
    (continuous_finsetSum m (fun i hi => (hq i hi).continuous.pow 2))
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (q i t)))
    (∑i∈m,(A i)^2) (-2) (by norm_num)
    (by
      intro t ht
      apply Finset.sum_le_sum
      intro i hi
      simpa using (sq_le_sq₀ (norm_nonneg _) (hA i hi)).mpr (h0 i hi t ht))
  have hv := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    (((finitePhysical_contDiffOn_offZero_C2 m q hq).continuousOn.pow 2).mono (fun x hx => hx.1))
    (fun _ _ => sq_nonneg _) hval.1 (fun t _ => native_finitePhysical_value_log_square m q t)
  have htime (i : AngularIndex) (hi : i∈m) (t : ℝ) (ht : t∈Ioo (-1:ℝ) 1) :
      finiteTimeLaplacian q i t^2≤2*((B i)^2+angularEnergyWeight i^4*(A i)^2) := by
    have hEig : 0≤angularEigenvalue i := by
      rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h <;> linarith
    have hcoeff : (angularEigenvalue i+1/4)^2≤angularEnergyWeight i^4 := by
      rw [show angularEnergyWeight i^4=(angularEnergyWeight i^2)^2 by ring,angularEnergyWeight_sq]
      nlinarith only [hEig]
    have hv0 : q i t^2≤(A i)^2 := by simpa using (sq_le_sq₀ (norm_nonneg _) (hA i hi)).mpr (h0 i hi t ht)
    have hv2 : deriv (deriv (q i)) t^2≤(B i)^2 := by simpa using (sq_le_sq₀ (norm_nonneg _) (hB i hi)).mpr (h2 i hi t ht)
    have hm := mul_le_mul hcoeff hv0 (sq_nonneg _) (by positivity : 0≤angularEnergyWeight i^4)
    unfold finiteTimeLaplacian
    nlinarith only [hv2,hm,sq_nonneg (deriv (deriv (q i)) t+(angularEigenvalue i+1/4)*q i t)]
  have hlap := native_exp_window_bound
    (continuous_finsetSum m (fun i hi => ((hq2 i hi).sub (continuous_const.mul (hq i hi).continuous)).pow 2))
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (finiteTimeLaplacian q i t)))
    (∑i∈m,2*((B i)^2+angularEnergyWeight i^4*(A i)^2)) 2 (by norm_num)
    (fun t ht => Finset.sum_le_sum (fun i hi => htime i hi t ht))
  have hl := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    (((continuousOn_nativeCoordinateLaplacian isClosed_singleton.isOpen_compl
      (finitePhysical_contDiffOn_offZero_C2 m q hq)).pow 2).mono (fun x hx => hx.1))
    (fun _ _ => sq_nonneg _) hlap.1 (fun t _ => native_finitePhysical_laplacian_log_square m q hq t)
  dsimp only
  have hb := add_le_add (hv.2.trans_le hval.2) (hl.2.trans_le hlap.2)
  simpa only [Finset.sum_add_distrib,mul_add,Pi.pow_apply] using hb

#print axioms native_exp_window_bound
#print axioms native_finitePhysical_window_energy
end Yamabe3.Analysis.SpherePolar
