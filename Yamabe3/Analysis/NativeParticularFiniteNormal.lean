import Yamabe3.Analysis.NativeContinuousNormalBudget
import Yamabe3.Analysis.NativeL2HalfNormalTrace

/-! Genuine sphere restriction of the derivatives of finite physical
particular fields, with the same original potential fixed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hm : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)

theorem nativeContinuousParticularNormal_coefficient (F : ℝ →ᵇ SpectralSpace AngularIndex) (i : AngularIndex) :
    let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm F
    let D := spectralFirstDerivativeConvolution nativeAngularRate (by norm_num) nativeAngularRate_lower (-2) (F-V • U) 0
    inner ℝ (angularBasis i) (nativeContinuousParticularNormal hκ0 hκ1 V hm F)=
      if 6≤angularEigenvalue i then -(D i)-(U 0 i)/2 else 0 := by
  dsimp only [nativeContinuousParticularNormal]
  rw [nativeHighProjection,nativeAngularProjection_coefficient]
  split_ifs
  · rw [inner_sub_right,inner_neg_right,real_inner_smul_right]
    simp only [←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply]
    ring
  · rfl

theorem nativeL2ParticularFinite_normal_trace_ae
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (s : Finset AngularIndex) :
    (fun θ : S => fderiv ℝ (fun x => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hm F i x) (θ:E) (θ:E))
      =ᵐ[angularVolume] (⇑(finiteHilbertProjection angularBasis s (nativeContinuousParticularNormal hκ0 hκ1 V hm F))) := by
  classical
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm F
  let D := spectralFirstDerivativeConvolution nativeAngularRate (by norm_num) nativeAngularRate_lower (-2) (F-V • U) 0
  let q := fun i t => Real.exp (-2*t)*U t i
  let s' := s.filter (fun i => 6≤angularEigenvalue i)
  have hq (i : AngularIndex) : ContDiff ℝ 2 (q i) :=
    (spectralIntegralPotentialInverse_physical_coordinate_C2 nativeAngularRate
      (by norm_num) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm F i).1
  have hdq (i : AngularIndex) : deriv (q i) 0=D i := by
    have hd := (lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).hasFDerivAt.comp_hasDerivAt 0
      (spectralIntegralPotentialInverse_weighted_hasDerivAt nativeAngularRate
        (by norm_num) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm F 0)
    change HasDerivAt (q i) (Real.exp (-2*0)*D i) 0 at hd
    simpa only [mul_zero,Real.exp_zero,one_mul] using hd.deriv
  have he (θ : S) :
      fderiv ℝ (fun x => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hm F i x) (θ:E) (θ:E)=
        projectedAngular s (fun _ => nativeContinuousParticularNormal hκ0 hκ1 V hm F) (0,θ) := by
    rw [nativeL2ParticularMode_sum]
    change fderiv ℝ (finitePhysical s' q) (θ:E) (θ:E)=_
    have hx : (θ:E)≠0 := by
      intro h
      have hn := norm_eq_of_mem_sphere θ
      rw [h,norm_zero] at hn
      norm_num at hn
    have hu := (finitePhysical_contDiffOn_offZero_C2 s' q (fun i _ => hq i)).contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds hx)
    have hr := native_finitePhysical_radial_derivative s' q (by norm_num : (0:ℝ)<1) θ
      (fun i _ => (hq i).differentiable (by norm_num) _)
      (by simpa only [one_smul] using hu.differentiableAt (by norm_num))
    have hscale : radialScale 1=1 := by simp [radialScale]
    simp only [one_smul,Real.log_one,neg_zero,hscale,div_one,neg_one_mul] at hr
    rw [hr]
    unfold finiteAngular projectedAngular
    rw [←Finset.sum_neg_distrib]
    simp only [s',Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [nativeContinuousParticularNormal_coefficient]
    change (if 6≤angularEigenvalue i then -((deriv (q i) 0+q i 0/2)*angularRepresentative i θ) else 0)=_
    split_ifs
    · rw [hdq]
      dsimp only [q]
      simp only [mul_zero,Real.exp_zero,one_mul]
      ring
    · simp
  have hf : (fun θ : S => fderiv ℝ (fun x => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hm F i x) (θ:E) (θ:E))=
      (fun θ => projectedAngular s (fun _ => nativeContinuousParticularNormal hκ0 hκ1 V hm F) (0,θ)) := funext he
  rw [hf]
  exact projectedAngular_ae s (fun _ => nativeContinuousParticularNormal hκ0 hκ1 V hm F) 0

#print axioms nativeContinuousParticularNormal_coefficient
#print axioms nativeL2ParticularFinite_normal_trace_ae
end Yamabe3.Analysis.SpherePolar
