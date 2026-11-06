import Yamabe3.Analysis.SpectralL2ContinuousRepresentative
import Yamabe3.Analysis.L2RealPairingBound

/-! The same actual free convolution is a bounded linear map from L2
to bounded continuous curves. Its value at the entrance is a genuine
bounded evaluation, not a choice of an L2 representative at one point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Convolution_uniform_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (t : ℝ) :
    ‖spectralL2Convolution k hk₀ hk δ F t‖ ≤
      (eLpNorm (spectralMajorant k₀ δ) 2).toReal*‖F‖ := by
  have hK := spectralMajorant_translate_memLp hk₀ hδ t
  have hi := hK.integrable_mul (Lp.memLp F).norm
  have hb : ‖spectralL2Convolution k hk₀ hk δ F t‖ ≤
      ∫ s,spectralMajorant k₀ δ (t-s)*‖F s‖ := by
    apply norm_integral_le_of_norm_le hi
    exact Eventually.of_forall fun s =>
      ((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))
  apply hb.trans
  have hn := integral_mul_le_eLpNorm_two volume hK (Lp.memLp F).norm
  have he := eLpNorm_comp_measurePreserving (p := (2:ℝ≥0∞))
    (spectralMajorant_memLp_two hk₀ hδ).1 (volume.measurePreserving_sub_left t)
  change eLpNorm (fun s => spectralMajorant k₀ δ (t-s)) 2=eLpNorm (spectralMajorant k₀ δ) 2 at he
  simpa only [he,eLpNorm_norm,Lp.norm_def] using hn

def spectralL2SmoothCurve {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : ℝ →ᵇ SpectralSpace ι :=
  BoundedContinuousFunction.ofNormedAddCommGroup (spectralL2Convolution k hk₀ hk δ F)
    (spectralL2Convolution_continuous k hk₀ hk hδ F (Lp.memLp F))
    ((eLpNorm (spectralMajorant k₀ δ) 2).toReal*‖F‖)
    (by intro t; exact spectralL2Convolution_uniform_norm_le k hk₀ hk hδ F t)

theorem spectralL2SmoothCurve_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ‖spectralL2SmoothCurve k hk₀ hk hδ F‖ ≤ (eLpNorm (spectralMajorant k₀ δ) 2).toReal*‖F‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun t => spectralL2Convolution_uniform_norm_le k hk₀ hk hδ F t)

theorem spectralL2SmoothCurve_add {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F G : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2SmoothCurve k hk₀ hk hδ (F+G)=spectralL2SmoothCurve k hk₀ hk hδ F+spectralL2SmoothCurve k hk₀ hk hδ G := by
  apply BoundedContinuousFunction.ext
  intro t
  change spectralL2Convolution k hk₀ hk δ ⇑(F+G) t=spectralL2Convolution k hk₀ hk δ F t+spectralL2Convolution k hk₀ hk δ G t
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ (Lp.coeFn_add F G)]
  unfold spectralL2Convolution
  simp only [Pi.add_apply,map_add]
  exact integral_add (spectralL2Convolution_everywhere_integrable k hk₀ hk hδ F (Lp.memLp F) t)
    (spectralL2Convolution_everywhere_integrable k hk₀ hk hδ G (Lp.memLp G) t)

theorem spectralL2SmoothCurve_smul {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (c : ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2SmoothCurve k hk₀ hk hδ (c • F)=c • spectralL2SmoothCurve k hk₀ hk hδ F := by
  apply BoundedContinuousFunction.ext
  intro t
  change spectralL2Convolution k hk₀ hk δ ⇑(c • F) t=c • spectralL2Convolution k hk₀ hk δ F t
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ (Lp.coeFn_smul c F),spectralL2Convolution_smul]
  rfl

def spectralL2SmoothingCLM {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  ({toFun := spectralL2SmoothCurve k hk₀ hk hδ
    map_add' := spectralL2SmoothCurve_add k hk₀ hk hδ
    map_smul' := spectralL2SmoothCurve_smul k hk₀ hk hδ} :
      Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →ₗ[ℝ] (ℝ →ᵇ SpectralSpace ι)).mkContinuous
    (eLpNorm (spectralMajorant k₀ δ) 2).toReal (by intro F;exact spectralL2SmoothCurve_norm_le k hk₀ hk hδ F)

#print axioms spectralL2Convolution_uniform_norm_le
#print axioms spectralL2SmoothCurve_add
#print axioms spectralL2SmoothCurve_smul
end Yamabe3.Analysis.Delaunay
