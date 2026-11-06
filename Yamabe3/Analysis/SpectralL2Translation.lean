import Yamabe3.Analysis.L2TimeTranslation
import Yamabe3.Analysis.SpectralL2FixedPointUnique

/-! The same whole-line resolvent is covariant under actual translations
of both source and potential. This supports uniform collars along one
half-end instead of independently selecting new solutions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

 theorem spectralL2Convolution_translate {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (δ a : ℝ) (F : ℝ → SpectralSpace ι) (t : ℝ) :
    spectralL2Convolution k hk₀ hk δ (fun s => F (s+a)) t=
      spectralL2Convolution k hk₀ hk δ F (t+a) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun s : ℝ => weightedSpectralKernel k hk₀ hk δ (t+a-s) (F s)) a
  simpa only [spectralL2Convolution,add_sub_add_right_eq_sub] using h

 theorem spectralL2FreeCLM_translate {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (hδ : |δ|<k₀) (a : ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    l2TimeTranslateCLM (SpectralSpace ι) a (spectralL2FreeCLM k hk₀ hk hδ F)=
      spectralL2FreeCLM k hk₀ hk hδ (l2TimeTranslateCLM (SpectralSpace ι) a F) := by
  apply Lp.ext
  have hR := spectralL2Resolvent_coe_ae k hk₀ hk hδ F
  have hRa := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hR
  have hT := spectralL2Resolvent_coe_ae k hk₀ hk hδ (l2TimeTranslateCLM (SpectralSpace ι) a F)
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ (l2TimeTranslate_ae (SpectralSpace ι) a F)] at hT
  filter_upwards [l2TimeTranslate_ae (SpectralSpace ι) a (spectralL2FreeCLM k hk₀ hk hδ F),hRa,hT] with t ht hr hu
  change (l2TimeTranslateCLM (SpectralSpace ι) a (spectralL2FreeCLM k hk₀ hk hδ F) : ℝ → SpectralSpace ι) t=_
  rw [ht]
  have hrr : (spectralL2FreeCLM k hk₀ hk hδ F : ℝ → SpectralSpace ι) (t+a)=
      spectralL2Convolution k hk₀ hk δ F (t+a) := hr
  have huu : (spectralL2FreeCLM k hk₀ hk hδ (l2TimeTranslateCLM (SpectralSpace ι) a F) : ℝ → SpectralSpace ι) t=
      spectralL2Convolution k hk₀ hk δ (fun s => F (s+a)) t := hu
  rw [hrr,huu,spectralL2Convolution_translate]

 theorem spectralL2PotentialMul_translate {ι : Type*} (a : ℝ) (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    l2TimeTranslateCLM (SpectralSpace ι) a (spectralL2PotentialMulCLM V F)=
      spectralL2PotentialMulCLM (boundedTimeTranslate ℝ a V) (l2TimeTranslateCLM (SpectralSpace ι) a F) := by
  apply Lp.ext
  have hm := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (spectralL2PotentialMul_coe_ae V F)
  filter_upwards [l2TimeTranslate_ae (SpectralSpace ι) a (spectralL2PotentialMulCLM V F),hm,
    spectralL2PotentialMul_coe_ae (boundedTimeTranslate ℝ a V) (l2TimeTranslateCLM (SpectralSpace ι) a F),
    l2TimeTranslate_ae (SpectralSpace ι) a F] with t ht hm hu hf
  change (l2TimeTranslateCLM (SpectralSpace ι) a (spectralL2PotentialMulCLM V F) : ℝ → SpectralSpace ι) t=_
  rw [ht]
  have hmm : (spectralL2PotentialMulCLM V F : ℝ → SpectralSpace ι) (t+a)=V (t+a) • F (t+a) := hm
  have huu : (spectralL2PotentialMulCLM (boundedTimeTranslate ℝ a V) (l2TimeTranslateCLM (SpectralSpace ι) a F) : ℝ → SpectralSpace ι) t=
      V (t+a) • (l2TimeTranslateCLM (SpectralSpace ι) a F : ℝ → SpectralSpace ι) t := hu
  rw [hmm,huu,hf]

 theorem spectralL2IntegralPotentialInverse_translate {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (hδ : |δ|<k₀) (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s*|V (t-s)|)≤κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s*|V (t-s)|)≤κ)
    (a : ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    l2TimeTranslateCLM (SpectralSpace ι) a (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)=
      spectralL2IntegralPotentialInverse k hk₀ hk hδ (boundedTimeTranslate ℝ a V) (l2TimeTranslateCLM (SpectralSpace ι) a F) := by
  apply spectralL2IntegralPotentialInverse_unique k hk₀ hk hδ hκ0 hκ1 (boundedTimeTranslate ℝ a V)
    (translated_kernel_bound V hminus a) (translated_kernel_bound V hplus a)
  conv_lhs => rw [spectralL2IntegralPotentialInverse_fixed k hk₀ hk hδ hκ0 hκ1 V hminus hplus F]
  rw [spectralL2FreeCLM_translate,map_sub,spectralL2PotentialMul_translate]

#print axioms spectralL2Convolution_translate
#print axioms spectralL2FreeCLM_translate
#print axioms spectralL2PotentialMul_translate
#print axioms spectralL2IntegralPotentialInverse_translate
end Yamabe3.Analysis.Delaunay
