import Yamabe3.Analysis.SpectralMajorantL2

/-! The actual free convolution of an L2 source is defined at every
real time and continuous. Point evaluation is thus attached to this
constructed representative, never to an arbitrary L2 representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Convolution_everywhere_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) :
    Integrable (fun s : ℝ => weightedSpectralKernel k hk₀ hk δ (t-s) (F s)) := by
  have hi := (spectralMajorant_translate_memLp hk₀ hδ t).integrable_mul hF.norm
  apply hi.mono'
  · have happly : Continuous (fun p : (SpectralSpace ι →L[ℝ] SpectralSpace ι) × SpectralSpace ι => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    exact happly.comp_aestronglyMeasurable
      ((((weightedSpectralKernel_continuous k hk₀ hk δ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable).prodMk hF.1)
  · exact Eventually.of_forall fun s =>
      ((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm (F s)).trans
        (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))

theorem spectralL2Convolution_continuous {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) :
    Continuous (spectralL2Convolution k hk₀ hk δ F) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have hi := ((spectralMajorant_translate_memLp hk₀ hδ t₀).integrable_mul hF.norm).const_mul
    (Real.exp (|δ|+k₀))
  apply continuousAt_of_dominated (bound := fun s => Real.exp (|δ|+k₀)*
    (spectralMajorant k₀ δ (t₀-s)*‖F s‖))
  · exact Eventually.of_forall fun t => (spectralL2Convolution_everywhere_integrable k hk₀ hk hδ F hF t).1
  · filter_upwards [Metric.ball_mem_nhds t₀ (by norm_num : (0:ℝ)<1)] with t ht
    have ht1 : |t-t₀|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using ht.le
    exact Eventually.of_forall fun s => by
      have he : Real.exp ((|δ|+k₀)*|t-t₀|) ≤ Real.exp (|δ|+k₀) := by
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg δ]
      calc
        ‖weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖ ≤ spectralMajorant k₀ δ (t-s)*‖F s‖ :=
          ((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))
        _ ≤ (Real.exp ((|δ|+k₀)*|t-t₀|)*spectralMajorant k₀ δ (t₀-s))*‖F s‖ :=
          mul_le_mul_of_nonneg_right (spectralMajorant_translate_le hk₀ t t₀ s) (norm_nonneg _)
        _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right he (mul_nonneg (spectralMajorant_nonneg hk₀ δ _) (norm_nonneg _))
  · exact hi
  · exact Eventually.of_forall fun s =>
      (((weightedSpectralKernel_continuous k hk₀ hk δ).comp (continuous_id.sub continuous_const)).clm_apply continuous_const).continuousAt

#print axioms spectralL2Convolution_everywhere_integrable
#print axioms spectralL2Convolution_continuous
end Yamabe3.Analysis.Delaunay
