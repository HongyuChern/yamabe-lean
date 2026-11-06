import Yamabe3.Analysis.NativeFinitePolarLaplacian
import Yamabe3.Analysis.NativePolarTimeWindow
import Yamabe3.Analysis.NativePoissonReflectedEnergy

/-! Actual Euclidean value and Laplacian energy on a collar crossing
r = 1. The bounds use the real finite angular Parseval identities and
the actual log-polar Jacobian; spectral norms are not renamed as jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_exp_window_integral_le {h : ℝ → ℝ} (hh : Integrable h)
    (hn : ∀ t,0 ≤ h t) (a : ℝ) (ha : |a| ≤ 2) :
    IntegrableOn (fun t => Real.exp (a*t)*h t) (Ioo (-1) 1) ∧
      (∫ t : ℝ in Ioo (-1) 1,Real.exp (a*t)*h t) ≤ Real.exp 2*(∫ t : ℝ,h t) := by
  have hb : ∀ t ∈ Ioo (-1:ℝ) 1,Real.exp (a*t) ≤ Real.exp 2 := by
    intro t ht
    apply Real.exp_le_exp.mpr
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    calc
      a*t ≤ |a*t| := le_abs_self _
      _ = |a| * |t| := abs_mul _ _
      _ ≤ 2*1 := mul_le_mul ha ht1 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hi : IntegrableOn (fun t => Real.exp (a*t)*h t) (Ioo (-1) 1) := by
    apply hh.integrableOn.bdd_mul (c := Real.exp 2) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hb t ht
  refine ⟨hi,?_⟩
  have hle := integral_mono_ae hi (hh.integrableOn.const_mul (Real.exp 2)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_le_mul_of_nonneg_right (hb t ht) (hn t))
  rw [integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hh (Eventually.of_forall hn)) (Real.exp_pos _).le)

theorem native_finitePhysical_collar_value_energy (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (hq : ∀ i ∈ s,ContDiff ℝ 2 (q i))
    (hI : ∀ i ∈ s,Integrable (fun t => q i t^2)) :
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    IntegrableOn (fun x => finitePhysical s q x^2) O ∧
      (∫ x in O,finitePhysical s q x^2) ≤ Real.exp 2*(∑ i ∈ s,∫ t : ℝ,q i t^2) := by
  have hs : Integrable (fun t => ∑ i ∈ s,q i t^2) := integrable_finsetSum s hI
  have he := native_exp_window_integral_le hs
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (q i t))) (-2) (by norm_num)
  have hp := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    (((finitePhysical_contDiffOn_offZero_C2 s q hq).continuousOn.pow 2).mono
      (fun x hx => hx.1)) (fun _ _ => sq_nonneg _) he.1
    (fun t _ => native_finitePhysical_value_log_square s q t)
  refine ⟨hp.1,hp.2.trans_le ?_⟩
  simpa only [integral_finsetSum s hI] using he.2

theorem native_finiteTimeLaplacian_energy (q : AngularIndex → ℝ → ℝ)
    (i : AngularIndex) (hq : ContDiff ℝ 2 (q i))
    (h0 : Integrable (fun t => q i t^2))
    (h2 : Integrable (fun t => deriv (deriv (q i)) t^2)) :
    Integrable (fun t => finiteTimeLaplacian q i t^2) ∧
      (∫ t : ℝ,finiteTimeLaplacian q i t^2) ≤
        2*((∫ t : ℝ,deriv (deriv (q i)) t^2)+angularEnergyWeight i^4*(∫ t : ℝ,q i t^2)) := by
  have hqc : ContDiff ℝ 1 (deriv (q i)) := (contDiff_succ_iff_deriv.mp hq).2.2
  have hqcc : Continuous (deriv (deriv (q i))) := hqc.continuous_deriv (by norm_num)
  have h0Lp := (memLp_two_iff_integrable_sq hq.continuous.aestronglyMeasurable).mpr h0
  have h2Lp := (memLp_two_iff_integrable_sq hqcc.aestronglyMeasurable).mpr h2
  have hi : Integrable (fun t => finiteTimeLaplacian q i t^2) :=
    (h2Lp.sub (h0Lp.const_mul (angularEigenvalue i+1/4))).integrable_sq
  have hEig : 0 ≤ angularEigenvalue i := by
    rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h <;> linarith
  have hc : (angularEigenvalue i+1/4)^2 ≤ angularEnergyWeight i^4 := by
    rw [show angularEnergyWeight i^4=(angularEnergyWeight i^2)^2 by ring,angularEnergyWeight_sq]
    nlinarith only [hEig]
  have hb (t : ℝ) : finiteTimeLaplacian q i t^2 ≤
      2*((deriv (deriv (q i)) t)^2+angularEnergyWeight i^4*q i t^2) := by
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (q i t))
    unfold finiteTimeLaplacian
    nlinarith only [hm,sq_nonneg (deriv (deriv (q i)) t+(angularEigenvalue i+1/4)*q i t)]
  refine ⟨hi,?_⟩
  have hm := (h2.add (h0.const_mul (angularEnergyWeight i^4))).const_mul 2
  have hle := integral_mono_ae hi hm (Eventually.of_forall hb)
  simpa only [integral_const_mul,integral_add' h2 (h0.const_mul (angularEnergyWeight i^4))] using hle

theorem native_finitePhysical_collar_laplacian_energy (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (hq : ∀ i ∈ s,ContDiff ℝ 2 (q i))
    (h0 : ∀ i ∈ s,Integrable (fun t => q i t^2))
    (h2 : ∀ i ∈ s,Integrable (fun t => deriv (deriv (q i)) t^2)) :
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    IntegrableOn (fun x => nativeCoordinateLaplacian (finitePhysical s q) x^2) O ∧
      (∫ x in O,nativeCoordinateLaplacian (finitePhysical s q) x^2) ≤
        2*Real.exp 2*(∑ i ∈ s,((∫ t : ℝ,deriv (deriv (q i)) t^2)+
          angularEnergyWeight i^4*(∫ t : ℝ,q i t^2))) := by
  have hI (i : AngularIndex) (hi : i ∈ s) := native_finiteTimeLaplacian_energy q i (hq i hi) (h0 i hi) (h2 i hi)
  have hs := integrable_finsetSum s (fun i hi => (hI i hi).1)
  have he := native_exp_window_integral_le hs
    (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg (finiteTimeLaplacian q i t))) 2 (by norm_num)
  have hp := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    (((continuousOn_nativeCoordinateLaplacian isClosed_singleton.isOpen_compl
      (finitePhysical_contDiffOn_offZero_C2 s q hq)).pow 2).mono (fun x hx => hx.1))
    (fun _ _ => sq_nonneg _) he.1
    (fun t _ => native_finitePhysical_laplacian_log_square s q hq t)
  refine ⟨hp.1,hp.2.trans_le (he.2.trans ?_)⟩
  rw [integral_finsetSum s (fun i hi => (hI i hi).1)]
  have hsum := Finset.sum_le_sum (fun i hi => (hI i hi).2)
  rw [← Finset.mul_sum] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (Real.exp_pos 2).le
  convert h using 1 <;> ring

#print axioms native_finitePhysical_collar_value_energy
#print axioms native_finiteTimeLaplacian_energy
#print axioms native_finitePhysical_collar_laplacian_energy
end Yamabe3.Analysis.SpherePolar
