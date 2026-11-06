import Yamabe3.Analysis.SpectralL2PotentialMul
import Yamabe3.Analysis.PositiveKernelAction

/-! Actual L2 free and potential convolutions are dominated by the same
positive kernel, including the same potential measure. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Convolution_enorm_le {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (δ : ℝ)
    (F : ℝ → SpectralSpace ι) (t : ℝ) :
    ‖spectralL2Convolution k hk₀ hk δ F t‖ₑ ≤
      positiveKernelAction volume (spectralPositiveKernel k₀ δ) (fun s => ‖F s‖ₑ) t := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro s
  have hb : ‖weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖ ≤ spectralMajorant k₀ δ (t-s)*‖F s‖ :=
    ((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm (F s)).trans
      (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))
  simpa only [spectralPositiveKernel,ENNReal.ofReal_mul (spectralMajorant_nonneg hk₀ δ (t-s)),ofReal_norm] using
    ENNReal.ofReal_le_ofReal hb

theorem spectralL2FreeCLM_enorm_ae {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ∀ᵐ t : ℝ,‖(spectralL2FreeCLM k hk₀ hk hδ F : ℝ → SpectralSpace ι) t‖ₑ ≤
      positiveKernelAction volume (spectralPositiveKernel k₀ δ) (fun s => ‖F s‖ₑ) t := by
  filter_upwards [spectralL2Resolvent_coe_ae k hk₀ hk hδ F] with t ht
  change ‖spectralL2Resolvent k hk₀ hk hδ F t‖ₑ ≤ _
  rw [ht]
  exact spectralL2Convolution_enorm_le k hk₀ hk δ F t

theorem spectralL2Potential_action_identity {ι : Type*} (k δ : ℝ) (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (t : ℝ) :
    positiveKernelAction volume (spectralPositiveKernel k δ)
      (fun s => ‖spectralL2PotentialMul V F s‖ₑ) t =
    positiveKernelAction (spectralPotentialMeasure V) (spectralPositiveKernel k δ)
      (fun s => ‖F s‖ₑ) t := by
  have hV : AEMeasurable (fun s => ENNReal.ofReal |V s|) volume := V.continuous.abs.measurable.ennreal_ofReal.aemeasurable
  have hK : Measurable (spectralPositiveKernel k δ t) :=
    (spectralPositiveKernel_measurable k δ).comp (measurable_const.prodMk measurable_id)
  have hf : AEMeasurable (fun s => ‖F s‖ₑ) volume := (Lp.memLp F).1.enorm
  have hp : AEMeasurable (fun s => spectralPositiveKernel k δ t s*‖F s‖ₑ) volume := hK.aemeasurable.mul hf
  unfold positiveKernelAction spectralPotentialMeasure
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul₀ hV hp]
  apply lintegral_congr_ae
  filter_upwards [spectralL2PotentialMul_coe_ae V F] with s hs
  dsimp only [Pi.mul_apply]
  rw [hs,enorm_smul,← ofReal_norm (V s),Real.norm_eq_abs]
  ac_rfl

theorem spectralL2FreePotential_enorm_ae {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ∀ᵐ t : ℝ,‖(spectralL2FreeCLM k hk₀ hk hδ (spectralL2PotentialMulCLM V F) : ℝ → SpectralSpace ι) t‖ₑ ≤
      positiveKernelAction (spectralPotentialMeasure V) (spectralPositiveKernel k₀ δ) (fun s => ‖F s‖ₑ) t := by
  filter_upwards [spectralL2FreeCLM_enorm_ae k hk₀ hk hδ (spectralL2PotentialMul V F)] with t ht
  rw [spectralL2Potential_action_identity] at ht
  exact ht

#print axioms spectralL2FreeCLM_enorm_ae
#print axioms spectralL2Potential_action_identity
#print axioms spectralL2FreePotential_enorm_ae
end Yamabe3.Analysis.Delaunay
