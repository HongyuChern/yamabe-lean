import Yamabe3.Analysis.NativeFullCollarSourceSupport
import Yamabe3.Analysis.NativePhysicalPairTestScaling

/-! The full physical collar return at one fixed time center. It retains
all angular modes and the exp(-5s/2) physical test factor. Its actual time
support is proved; no inner/outer source membership is presumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

def nativeShiftedFullCollarSourceReturnCLM (s:ℝ) : NativeCollarL2 →L[ℝ]
    Lp AngularSpectralSpace 2 (volume:Measure ℝ) :=
  (ContinuousLinearMap.adjoint (nativeL2FullPhysicalSourceCLM.comp
    (l2TimeTranslateCLM AngularSpectralSpace s))).comp
      (nativeCollarPotentialMulCLM (BoundedContinuousFunction.const ℝ (1:ℝ)))

theorem nativeShiftedFullCollarSourceReturn_physical_test (s:ℝ) (U:NativeCollarL2)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    inner ℝ (nativeShiftedFullCollarSourceReturnCLM s U) (nativePhysicalPairTestL2 φ hφ hc h0)=
      Real.exp (-5*s/2)*(∫x in nativePoissonEntranceCollar,U x*φ (Real.exp (-s) • x)) := by
  change inner ℝ ((ContinuousLinearMap.adjoint
    (nativeL2FullPhysicalSourceCLM.comp (l2TimeTranslateCLM AngularSpectralSpace s)))
      (nativeCollarPotentialMulCLM (BoundedContinuousFunction.const ℝ (1:ℝ)) U)) _=_
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [nativeCollarPotentialMulCLM_ae (BoundedContinuousFunction.const ℝ (1:ℝ)) U,
    nativePhysicalPairTestL2_shift_lift φ hφ hc h0 s,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hm ht hx
  simp only [RCLike.inner_apply,conj_trivial,ContinuousLinearMap.comp_apply,hm,ht]
  rw [nativePhysicalPairTest_scaling φ s (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))]
  change (‖x‖^2*Real.exp (-5*s/2)*φ (Real.exp (-s) • x))*((1/‖x‖^2)*U x)=_
  have hn:‖x‖≠0 := norm_ne_zero_iff.mpr (cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx))
  field_simp

theorem nativeShiftedFullCollarSourceReturn_time_support (s:ℝ) (U:NativeCollarL2) :
    ∀ᵐt:ℝ∂volume,t∉Icc (s-1/2) (s+1/2) → nativeShiftedFullCollarSourceReturnCLM s U t=0 := by
  let A:=(Icc (s-1/2) (s+1/2))ᶜ
  have hA:MeasurableSet A := measurableSet_Icc.compl
  let F:=nativeShiftedFullCollarSourceReturnCLM s U
  let Z:=nativeTimeCutL2 A hA F
  have hcut:∀ᵐt:ℝ∂volume,Z (t+s)=A.indicator (F:ℝ→AngularSpectralSpace) (t+s) :=
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae (nativeTimeCutL2_ae A hA F)
  have hz:nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s Z)=0 := by
    apply nativeL2FullPhysicalSource_zero_of_time_zero
    filter_upwards [l2TimeTranslate_ae AngularSpectralSpace s Z,hcut] with t ht hc
    intro hi
    have htA:t+s∉A := by
      intro h
      exact h ⟨by linarith [hi.1],by linarith [hi.2]⟩
    rw [ht,hc,indicator_of_notMem htA]
  have hi:inner ℝ F Z=0 := by
    change inner ℝ ((ContinuousLinearMap.adjoint
      (nativeL2FullPhysicalSourceCLM.comp (l2TimeTranslateCLM AngularSpectralSpace s)))
        (nativeCollarPotentialMulCLM (BoundedContinuousFunction.const ℝ (1:ℝ)) U)) Z=0
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.comp_apply,hz,inner_zero_right]
  have hZ:Z=0 := by
    have he:=nativeTimeCutL2_inner A hA F
    change inner ℝ F Z=‖Z‖^2 at he
    rw [hi] at he
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
  have hcoe:=nativeTimeCutL2_ae A hA F
  change (Z:ℝ→AngularSpectralSpace)=ᵐ[volume] _ at hcoe
  rw [hZ] at hcoe
  filter_upwards [hcoe,Lp.coeFn_zero AngularSpectralSpace 2 (volume:Measure ℝ)] with t ht hz
  intro hc
  rw [indicator_of_mem (show t∈A from hc)] at ht
  exact ht.symm.trans hz

#print axioms nativeShiftedFullCollarSourceReturn_physical_test
#print axioms nativeShiftedFullCollarSourceReturn_time_support
end Yamabe3.Analysis.SpherePolar
