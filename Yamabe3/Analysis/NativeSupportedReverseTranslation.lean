import Yamabe3.Analysis.NativeLowSourceLocality
import Yamabe3.Analysis.L2TimeTranslation

/-! Support-aware covariance of the same prepared source. The reflected
time translation and exp(-4s) factor are identified in L2, so all scaled
low source equations refer to one original source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeL2_lower_support_translate (b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    ∀ᵐt : ℝ ∂volume,t<b-s → l2TimeTranslateCLM AngularSpectralSpace s F t=0 := by
  have hs := (measurePreserving_add_right volume s).quasiMeasurePreserving.ae hF
  filter_upwards [l2TimeTranslate_ae AngularSpectralSpace s F,hs] with t ht hh
  intro h
  change l2TimeTranslateCLM AngularSpectralSpace s F t=0
  rw [ht]
  exact hh (by linarith)

theorem nativeSupportedReverseSource_translate (b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    l2TimeTranslateCLM AngularSpectralSpace (-s) (nativeSupportedReverseSourcePrepareCLM b F)=
      Real.exp (-4*s) • nativeSupportedReverseSourcePrepareCLM (b-s) (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  let H := nativeSupportedReverseSourcePrepareCLM b F
  let Fs := l2TimeTranslateCLM AngularSpectralSpace s F
  let Q := nativeSupportedReverseSourcePrepareCLM (b-s) Fs
  have hf := nativeL2_lower_support_translate b s F hF
  have hA := (measurePreserving_add_right volume s).quasiMeasurePreserving.ae
    (nativeSupportedReverseSourcePrepare_ae b F hF)
  have hT := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (l2TimeTranslate_ae AngularSpectralSpace (-s) H)
  have hQ := nativeSupportedReverseSourcePrepare_ae (b-s) Fs hf
  have he : (fun t : ℝ => l2TimeTranslateCLM AngularSpectralSpace (-s) H (-t))=ᵐ[volume]
      (fun t => Real.exp (-4*s) • Q (-t)) := by
    filter_upwards [hT,hA,hQ,l2TimeTranslate_ae AngularSpectralSpace s F] with t ht ha hq hft
    change l2TimeTranslateCLM AngularSpectralSpace (-s) H (-t)=H (-t+ -s) at ht
    change H (-(t+s))=Real.exp (-4*(t+s)) • F (t+s) at ha
    change Q (-t)=Real.exp (-4*t) • Fs t at hq
    change Fs t=F (t+s) at hft
    rw [ht,show -t+ -s= -(t+s) by ring,ha,hq,hft,smul_smul,←Real.exp_add]
    congr 2
    ring
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae he
  apply Lp.ext
  filter_upwards [hn,Lp.coeFn_smul (Real.exp (-4*s)) Q] with t ht hc
  change l2TimeTranslateCLM AngularSpectralSpace (-s) H t=(Real.exp (-4*s) • Q) t
  rw [hc]
  change l2TimeTranslateCLM AngularSpectralSpace (-s) H t=Real.exp (-4*s) • Q t
  simpa only [neg_neg] using ht

theorem nativeSupportedReverseSource_all_scale_reconstruction (b s : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    Real.exp (4*s) • nativeLowReverseL2SourceCLM
      (l2TimeTranslateCLM AngularSpectralSpace (-s) (nativeSupportedReverseSourcePrepareCLM b F))=
        nativeL2LowPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F) := by
  rw [nativeSupportedReverseSource_translate b s F hF,map_smul,smul_smul,
    ←Real.exp_add,show 4*s+-4*s=0 by ring,Real.exp_zero,one_smul]
  exact nativeSupportedReverseSource_local_reconstruction (b-s) _ (nativeL2_lower_support_translate b s F hF)

#print axioms nativeL2_lower_support_translate
#print axioms nativeSupportedReverseSource_translate
#print axioms nativeSupportedReverseSource_all_scale_reconstruction
end Yamabe3.Analysis.SpherePolar
