import Yamabe3.Analysis.NativeFiniteOuterWindowSource
import Yamabe3.Analysis.NativeFullCollarSourceSupport

/-! Actual time support of the full adjoint shell returns, and of the
finite exterior-window source. The fixed lower support is proved from
duality, not assumed from the physical name of the source operator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

theorem nativeFullShellSourceReturn_time_support (s:ℝ) (U:NativeCollarL2) :
    ∀ᵐt:ℝ∂volume,t∉Icc (s-1/2) (s+1/2) → nativeFullShellSourceReturnCLM s U t=0 := by
  let A:=(Icc (s-1/2) (s+1/2))ᶜ
  have hA:MeasurableSet A := measurableSet_Icc.compl
  let F:=nativeFullShellSourceReturnCLM s U
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
        (nativeShellSourceWeightCLM U)) Z=0
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

theorem nativeFiniteOuterWindowSource_lower_support
    {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m:ℕ) (rows:Fin m→X →L[ℝ] NativeCollarL2) (x:X) :
    ∀ᵐt:ℝ∂volume,t < -(m:ℝ)/2-1 → nativeFiniteOuterWindowSourceCLM m rows x t=0 := by
  let Fs:Fin m→Lp AngularSpectralSpace 2 (volume:Measure ℝ) :=
    fun i=>nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i) (rows i x)
  have hzero:∀i:Fin m,∀ᵐt:ℝ∂volume,t < -(m:ℝ)/2-1 → Fs i t=0 := by
    intro i
    filter_upwards [nativeFullShellSourceReturn_time_support (nativeOuterLogShellCenter i) (rows i x)] with t ht
    intro hb
    apply ht
    intro hI
    have hn:(i.val:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
    dsimp only [nativeOuterLogShellCenter] at hI
    linarith [hI.1]
  have hall:∀ᵐt:ℝ∂volume,∀i:Fin m,t < -(m:ℝ)/2-1 → Fs i t=0 := ae_all_iff.mpr hzero
  have hsum:(((∑i:Fin m,Fs i):Lp AngularSpectralSpace 2 (volume:Measure ℝ)):ℝ→AngularSpectralSpace)=ᵐ[volume] (fun t=>∑i:Fin m,Fs i t) :=
    Lp.coeFn_fun_finsetSum Finset.univ Fs
  have he:nativeFiniteOuterWindowSourceCLM m rows x=∑i:Fin m,Fs i := by
    simp only [nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,Fs]
  rw [he]
  filter_upwards [hsum,hall] with t ht hz
  intro hb
  rw [ht]
  exact Finset.sum_eq_zero (fun i _=>hz i hb)

#print axioms nativeFullShellSourceReturn_time_support
#print axioms nativeFiniteOuterWindowSource_lower_support
end Yamabe3.Analysis.SpherePolar
