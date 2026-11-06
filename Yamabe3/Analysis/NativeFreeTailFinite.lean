import Yamabe3.Analysis.NativeC2CollarSeries
import Yamabe3.Analysis.NativeCollarSeriesIdentification

/-! Uniform actual Euclidean energy of finite free high Poisson fields
at every tail scale s>=1. Only the true L2 boundary coefficients occur;
no fourth-order boundary regularity is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeFreeTailCoefficient (s : ℝ) (b : SpectralSpace AngularIndex) (i : AngularIndex) (t : ℝ) : ℝ :=
  Real.exp (2*s-nativeAngularRate i*(t+s))*(if 6 ≤ angularEigenvalue i then b i else 0)

theorem nativeFreeTailCoefficient_C2 (s : ℝ) (b : SpectralSpace AngularIndex) (i : AngularIndex) :
    ContDiff ℝ 2 (nativeFreeTailCoefficient s b i) := by
  unfold nativeFreeTailCoefficient
  fun_prop

private theorem coefficient_deriv (s : ℝ) (b : SpectralSpace AngularIndex) (i : AngularIndex) (t : ℝ) :
    HasDerivAt (nativeFreeTailCoefficient s b i)
      (-nativeAngularRate i*nativeFreeTailCoefficient s b i t) t := by
  have h := (((hasDerivAt_const t (2*s)).sub
    (((hasDerivAt_id t).add_const s).const_mul (nativeAngularRate i))).exp).mul_const
      (if 6 ≤ angularEigenvalue i then b i else 0)
  change HasDerivAt (nativeFreeTailCoefficient s b i)
    (Real.exp (2*s-nativeAngularRate i*(t+s))*(0-nativeAngularRate i*1)*
      (if 6 ≤ angularEigenvalue i then b i else 0)) t at h
  convert h using 1
  dsimp only [nativeFreeTailCoefficient]
  ring

 theorem nativeFreeTailCoefficient_equation (s : ℝ) (b : SpectralSpace AngularIndex) (i : AngularIndex) :
    finiteTimeLaplacian (nativeFreeTailCoefficient s b) i=0 := by
  have hd : deriv (nativeFreeTailCoefficient s b i)=fun t => -nativeAngularRate i*nativeFreeTailCoefficient s b i t :=
    funext fun t => (coefficient_deriv s b i t).deriv
  funext t
  unfold finiteTimeLaplacian
  rw [hd,((coefficient_deriv s b i t).const_mul (-nativeAngularRate i)).deriv]
  by_cases hi : 6 ≤ angularEigenvalue i
  · have hk : nativeAngularRate i^2=angularEigenvalue i+1/4 := by rw [nativeAngularRate_sq,max_eq_right hi]
    change _=0
    calc
      _=(nativeAngularRate i^2-(angularEigenvalue i+1/4))*nativeFreeTailCoefficient s b i t := by ring
      _=0 := by rw [hk,sub_self,zero_mul]
  · simp only [nativeFreeTailCoefficient,if_neg hi,mul_zero,sub_zero,Pi.zero_apply]

 theorem nativeFreeTailCoefficient_bound (s : ℝ) (hs : 1 ≤ s)
    (b : SpectralSpace AngularIndex) (i : AngularIndex) (t : ℝ) (ht : t∈Ioo (-1:ℝ) 1) :
    nativeFreeTailCoefficient s b i t^2 ≤ Real.exp 4*(b i)^2 := by
  have hk := nativeAngularRate_lower i
  have hex : 2*s-nativeAngularRate i*(t+s) ≤ 2 := by
    have hp : 0 ≤ (nativeAngularRate i-2)*(s-1) := mul_nonneg (by linarith) (by linarith)
    have ht' : 0 ≤ nativeAngularRate i*(t+1) := mul_nonneg (by linarith) (by linarith [ht.1])
    nlinarith only [hp,ht']
  unfold nativeFreeTailCoefficient
  split_ifs with hi
  · rw [mul_pow,←Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (by norm_num;linarith)
  · simp only [mul_zero,zero_pow (by decide : 2≠0)]
    positivity

 theorem nativeFreeTailFinite_laplacian_zero (s : ℝ) (b : SpectralSpace AngularIndex)
    (m : Finset AngularIndex) {x : E} (hx : x≠0) :
    nativeCoordinateLaplacian (finitePhysical m (nativeFreeTailCoefficient s b)) x=0 := by
  rw [native_finitePhysical_laplacian m _ (fun i _ => nativeFreeTailCoefficient_C2 s b i) hx]
  have he : finiteAngular m (finiteTimeLaplacian (nativeFreeTailCoefficient s b))=fun _ => 0 := by
    funext p
    simp only [finiteAngular,nativeFreeTailCoefficient_equation,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
  rw [he]
  by_cases hx' : x=0
  · subst x;rw [cylinderLift_zero,zero_div]
  · change cylinderLift (fun _ => 0) (⟨x,hx'⟩ : puncturedSpace)/‖x‖^2=0
    rw [cylinderLift_coe]
    simp [puncturedCylinderLift]

 theorem nativeFreeTailFinite_energy (s : ℝ) (hs : 1 ≤ s) (b : SpectralSpace AngularIndex)
    (m : Finset AngularIndex) :
    ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),finitePhysical m (nativeFreeTailCoefficient s b) x^2)+
      (∫ x in nativePolarTimeWindow (Ioo (-1) 1),
        nativeCoordinateLaplacian (finitePhysical m (nativeFreeTailCoefficient s b)) x^2)) ≤ 
          (2*Real.exp 6)*(∑ i ∈ m,(b i)^2) := by
  let q := nativeFreeTailCoefficient s b
  have hq (i : AngularIndex) : ContDiff ℝ 2 (q i) := nativeFreeTailCoefficient_C2 s b i
  have hc : Continuous (fun t : ℝ => Real.exp (-2*t)*(∑ i ∈ m,q i t^2)) := by
    apply Continuous.mul
    · fun_prop
    · exact continuous_finsetSum _ (fun i _ => (hq i).continuous.pow 2)
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-2*t)*(∑ i ∈ m,q i t^2)) (Ioo (-1) 1) (volume : Measure ℝ) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hp := native_timeWindow_integrable_and_integral_of_angular_energy
    (Ioo (-1) 1) measurableSet_Ioo
    (((finitePhysical_contDiffOn_offZero_C2 m q (fun i _ => hq i)).continuousOn.pow 2).mono
      (fun x hx => hx.1)) (fun _ _ => sq_nonneg _) hi
    (fun t _ => native_finitePhysical_value_log_square m q t)
  have he : (fun x => nativeCoordinateLaplacian (finitePhysical m q) x^2)=ᵐ[volume.restrict
      (nativePolarTimeWindow (Ioo (-1) 1))] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open 1).measurableSet] with x hx
    rw [nativeFreeTailFinite_laplacian_zero s b m hx.1,zero_pow (by decide : 2≠0)]
  rw [integral_congr_ae he,integral_zero,add_zero]
  have hb : ∀ t∈Ioo (-1:ℝ) 1,Real.exp (-2*t)*(∑ i ∈ m,q i t^2) ≤ Real.exp 6*(∑ i ∈ m,(b i)^2) := by
    intro t ht
    have hqsum := Finset.sum_le_sum (fun i (_ : i∈m) => nativeFreeTailCoefficient_bound s hs b i t ht)
    rw [←Finset.mul_sum] at hqsum
    calc
      _  ≤  Real.exp 2*(Real.exp 4*(∑ i ∈ m,(b i)^2)) :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht.1])) hqsum
          (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Real.exp_pos _).le
      _ = _ := by rw [←mul_assoc,←Real.exp_add];norm_num
  have hle := setIntegral_mono_on hi ((continuous_const : Continuous (fun _ : ℝ => Real.exp 6*(∑ i ∈ m,(b i)^2))).integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo hb
  norm_num [integral_const,Real.volume_Ioo] at hle
  exact hp.2.trans_le (by simpa only [neg_mul,mul_assoc] using hle)

#print axioms nativeFreeTailCoefficient_C2
#print axioms nativeFreeTailCoefficient_equation
#print axioms nativeFreeTailCoefficient_bound
#print axioms nativeFreeTailFinite_laplacian_zero
#print axioms nativeFreeTailFinite_energy
end Yamabe3.Analysis.SpherePolar
