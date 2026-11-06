import Yamabe3.Analysis.NativeFullCollarSourceReturn

/-! The actual adjoint collar source return has finite time support.
This is proved from the polar L2 integral and adjoint duality, not assumed
from the name of the return map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

def nativeTimeCutL2 (s : Set ℝ) (hs : MeasurableSet s)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  ((Lp.memLp F).indicator hs).toLp (s.indicator (F : ℝ → AngularSpectralSpace))

theorem nativeTimeCutL2_ae (s : Set ℝ) (hs : MeasurableSet s)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (nativeTimeCutL2 s hs F : ℝ → AngularSpectralSpace)=ᵐ[volume] s.indicator (F : ℝ → AngularSpectralSpace) :=
  ((Lp.memLp F).indicator hs).coeFn_toLp

theorem nativeTimeCutL2_inner (s : Set ℝ) (hs : MeasurableSet s)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    inner ℝ F (nativeTimeCutL2 s hs F)=‖nativeTimeCutL2 s hs F‖^2 := by
  rw [←real_inner_self_eq_norm_sq (nativeTimeCutL2 s hs F),L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeTimeCutL2_ae s hs F] with t ht
  rw [ht]
  by_cases h : t∈s
  · rw [indicator_of_mem h]
  · simp only [indicator_of_notMem h,inner_zero_right]

theorem nativeL2CollarLift_zero_of_time_zero
    (F : Lp AngularL2 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t∈Icc (-(1/2:ℝ)) (1/2) → F t=0) :
    nativeL2CollarLiftCLM F=0 := by
  have hw := nativeAngularL2Joint_measurable F
  have hae : ∀ᵐt : ℝ ∂volume,(fun θ => nativeAngularL2Joint F (t,θ))=ᵐ[angularVolume] (F t : S → ℝ) :=
    Eventually.of_forall (nativeAngularL2Joint_ae F)
  have hm := memLp_cylinderLift_on_shell hw (-(1/2:ℝ)) (1/2)
    (native_joint_memLp_interval_of_memLp (Lp.memLp F) hw hae _ _)
  have hsub := setIntegral_mono_set (s := nativePoissonEntranceCollar) hm.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (cylinderLift (nativeAngularL2Joint F) x))
    (Eventually.of_forall fun x hx => nativeEntranceCollar_subset_shell hx)
  rw [native_L2_shell_square (Lp.memLp F) hw hae] at hsub
  have hi : (∫t in Icc (-(1/2:ℝ)) (1/2),Real.exp (-2*t)*‖F t‖^2)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hF,ae_restrict_mem measurableSet_Icc] with t ht htc
    simp only [ht htc,norm_zero,zero_pow (by decide : 2≠0),mul_zero,Pi.zero_apply]
  rw [hi] at hsub
  have he := native_norm_toLp_sq_eq_integral_sq (nativeL2_lift_memLp_collar (Lp.memLp F) hw hae)
  change ‖nativeL2CollarLiftCLM F‖^2=_ at he
  have hn : ‖nativeL2CollarLiftCLM F‖=0 := by
    rw [←he] at hsub
    nlinarith [norm_nonneg (nativeL2CollarLiftCLM F)]
  exact norm_eq_zero.mp hn

theorem nativeL2FullPhysicalSource_zero_of_time_zero
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t∈Icc (-(1/2:ℝ)) (1/2) → F t=0) :
    nativeL2FullPhysicalSourceCLM F=0 := by
  apply nativeL2CollarLift_zero_of_time_zero
  filter_upwards [nativeL2FullAngularCLM_ae F,hF] with t ht hf
  intro h
  change nativeL2FullAngularCLM F t=0
  rw [ht,hf h]
  exact map_zero _

theorem nativeFullCollarSourceReturn_time_support (U : NativeCollarL2) :
    ∀ᵐt : ℝ ∂volume,t∉Icc (-(1/2:ℝ)) (1/2) → nativeFullCollarSourceReturnCLM U t=0 := by
  let s := (Icc (-(1/2:ℝ)) (1/2))ᶜ
  have hs : MeasurableSet s := measurableSet_Icc.compl
  let F := nativeFullCollarSourceReturnCLM U
  let Z := nativeTimeCutL2 s hs F
  have hz : nativeL2FullPhysicalSourceCLM Z=0 := by
    apply nativeL2FullPhysicalSource_zero_of_time_zero
    filter_upwards [nativeTimeCutL2_ae s hs F] with t ht
    intro h
    rw [ht,indicator_of_notMem (show t∉s from fun hc => hc h)]
  have hi : inner ℝ F Z=0 := by
    change inner ℝ ((ContinuousLinearMap.adjoint nativeL2FullPhysicalSourceCLM)
      (nativeCollarPotentialMulCLM (BoundedContinuousFunction.const ℝ (1:ℝ)) U)) Z=0
    rw [ContinuousLinearMap.adjoint_inner_left,hz,inner_zero_right]
  have hZ : Z=0 := by
    have he := nativeTimeCutL2_inner s hs F
    change inner ℝ F Z=‖Z‖^2 at he
    rw [hi] at he
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
  have hzcoe := Lp.coeFn_zero AngularSpectralSpace 2 (volume : Measure ℝ)
  have hcoe := nativeTimeCutL2_ae s hs F
  change (Z : ℝ → AngularSpectralSpace)=ᵐ[volume] _ at hcoe
  rw [hZ] at hcoe
  filter_upwards [hcoe,hzcoe] with t ht hz
  intro hc
  rw [indicator_of_mem (show t∈s from hc)] at ht
  exact ht.symm.trans hz

#print axioms nativeTimeCutL2_ae
#print axioms nativeTimeCutL2_inner
#print axioms nativeL2CollarLift_zero_of_time_zero
#print axioms nativeL2FullPhysicalSource_zero_of_time_zero
#print axioms nativeFullCollarSourceReturn_time_support
end Yamabe3.Analysis.SpherePolar
