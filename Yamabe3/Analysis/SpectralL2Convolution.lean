import Yamabe3.Analysis.BochnerKernelSchur
import Yamabe3.Analysis.SpectralPositiveKernel

/-! Actual Hilbert-valued diagonal convolution on L2 source functions.
It uses the same weighted kernel as the bounded-continuous source solver;
no time continuity of the new source is required. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralL2Convolution {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (δ : ℝ)
    (F : ℝ → SpectralSpace ι) (t : ℝ) : SpectralSpace ι :=
  ∫ s : ℝ,weightedSpectralKernel k hk₀ hk δ (t-s) (F s)

theorem spectralL2Convolution_integrable_memLp {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : StronglyMeasurable F) (hF2 : MemLp F 2) :
    (∀ᵐ t : ℝ,Integrable (fun s : ℝ => weightedSpectralKernel k hk₀ hk δ (t-s) (F s))) ∧
      MemLp (spectralL2Convolution k hk₀ hk δ F) 2 := by
  have hA : StronglyMeasurable (fun p : ℝ × ℝ => weightedSpectralKernel k hk₀ hk δ (p.1-p.2)) :=
    ((weightedSpectralKernel_continuous k hk₀ hk δ).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable
  have happly : Continuous (fun p : (SpectralSpace ι →L[ℝ] SpectralSpace ι) × SpectralSpace ι => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hT : StronglyMeasurable (fun p : ℝ × ℝ => weightedSpectralKernel k hk₀ hk δ (p.1-p.2) (F p.2)) :=
    happly.comp_stronglyMeasurable (hA.prodMk (hF.comp_measurable measurable_snd))
  have hm : Measurable (fun t => ‖F t‖ₑ) := hF.enorm
  have hfin : (∫⁻ t : ℝ,‖F t‖ₑ^2)<⊤ := by
    simpa only [ENNReal.toReal_ofNat,ENNReal.rpow_two] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞)≠0) (by simp) hF2.2)
  have hneg : |-δ|<k₀ := by simpa only [abs_neg] using hδ
  have hc (s : ℝ) : (∫⁻ t,spectralPositiveKernel k₀ δ t s) ≤ ENNReal.ofReal (1/(k₀^2-δ^2)) := by
    have he (t : ℝ) : spectralPositiveKernel k₀ δ t s=spectralPositiveKernel k₀ (-δ) s t :=
      congrFun (congrFun (spectralPositiveKernel_flip k₀ δ) s) t
    simp_rw [he]
    simpa only [neg_sq] using (spectralPositiveKernel_row_mass hk₀ hneg s).le
  apply bochner_kernel_schur_integrable_memLp volume volume
    (spectralPositiveKernel_measurable k₀ δ) ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    (fun t => (spectralPositiveKernel_row_mass hk₀ hδ t).le) hc hm hfin (fun t s => weightedSpectralKernel k hk₀ hk δ (t-s) (F s)) hT
  intro t s
  have hb : ‖weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖ ≤ spectralMajorant k₀ δ (t-s)*‖F s‖ :=
    ((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm (F s)).trans
      (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))
  simpa only [spectralPositiveKernel,ENNReal.ofReal_mul (spectralMajorant_nonneg hk₀ δ (t-s)),ofReal_norm] using
    ENNReal.ofReal_le_ofReal hb

theorem spectralL2Convolution_eq_original {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    spectralL2Convolution k hk₀ hk δ F t=spectralConvolution k hk₀ hk δ F t := by
  have h := integral_sub_left_eq_self
    (fun s : ℝ => weightedSpectralKernel k hk₀ hk δ s (F (t-s))) volume t
  simpa only [spectralL2Convolution,spectralConvolution,sub_sub_cancel] using h

#print axioms spectralL2Convolution_integrable_memLp
#print axioms spectralL2Convolution_eq_original
end Yamabe3.Analysis.Delaunay
