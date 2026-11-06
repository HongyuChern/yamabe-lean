import Yamabe3.Analysis.SpectralL2Convolution
import Yamabe3.Analysis.BochnerL2NormBound

/-! Sharp denominator for the actual free L2 convolution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Convolution_eLpNorm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : StronglyMeasurable F) :
    eLpNorm (spectralL2Convolution k hk₀ hk δ F) 2 ≤
      ENNReal.ofReal (1/(k₀^2-δ^2))*eLpNorm F 2 := by
  have hneg : |-δ|<k₀ := by simpa only [abs_neg] using hδ
  have hc (s : ℝ) : (∫⁻ t,spectralPositiveKernel k₀ δ t s) ≤ ENNReal.ofReal (1/(k₀^2-δ^2)) := by
    have he (t : ℝ) : spectralPositiveKernel k₀ δ t s=spectralPositiveKernel k₀ (-δ) s t :=
      congrFun (congrFun (spectralPositiveKernel_flip k₀ δ) s) t
    simp_rw [he]
    simpa only [neg_sq] using (spectralPositiveKernel_row_mass hk₀ hneg s).le
  apply bochner_kernel_eLpNorm_le volume volume (spectralPositiveKernel_measurable k₀ δ)
    (fun t => (spectralPositiveKernel_row_mass hk₀ hδ t).le) hc hF
    (fun t s => weightedSpectralKernel k hk₀ hk δ (t-s) (F s))
  intro t s
  have hb : ‖weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖ ≤ spectralMajorant k₀ δ (t-s)*‖F s‖ :=
    ((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm (F s)).trans
      (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))
  simpa only [spectralPositiveKernel,ENNReal.ofReal_mul (spectralMajorant_nonneg hk₀ δ (t-s)),ofReal_norm] using
    ENNReal.ofReal_le_ofReal hb

theorem spectralL2Convolution_congr_ae {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (δ : ℝ)
    {F G : ℝ → SpectralSpace ι} (hFG : F=ᵐ[volume]G) :
    spectralL2Convolution k hk₀ hk δ F=spectralL2Convolution k hk₀ hk δ G := by
  funext t
  apply integral_congr_ae
  filter_upwards [hFG] with s hs
  rw [hs]

#print axioms spectralL2Convolution_eLpNorm_le
#print axioms spectralL2Convolution_congr_ae
end Yamabe3.Analysis.Delaunay
