import Yamabe3.Analysis.SpectralKernelIntegral
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# A true Hilbert-space convolution resolvent

This integrates the bounded diagonal operator against a Hilbert-valued
continuous source. The norm estimate is in C_b(R, lp 2), before taking any
coordinate. It therefore controls the full angular L2 norm at each time.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction Convolution
namespace Yamabe3.Analysis.Delaunay

/-- Actual Bochner time convolution with the diagonal operator kernel. -/
def spectralConvolution {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) : SpectralSpace ι :=
  ∫ s : ℝ, weightedSpectralKernel k hk₀ hk δ s (F (t - s))

private theorem spectral_integrand_bound {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ)
    (F : ℝ →ᵇ SpectralSpace ι) (t s : ℝ) :
    ‖weightedSpectralKernel k hk₀ hk δ s (F (t - s))‖ ≤
      spectralMajorant k₀ δ s * ‖F‖ := by
  calc
    _ ≤ ‖weightedSpectralKernel k hk₀ hk δ s‖ * ‖F (t - s)‖ :=
      (weightedSpectralKernel k hk₀ hk δ s).le_opNorm _
    _ ≤ spectralMajorant k₀ δ s * ‖F‖ :=
      mul_le_mul (weightedSpectralKernel_norm_le k hk₀ hk δ s)
        (F.norm_coe_le_norm _) (norm_nonneg _) (spectralMajorant_nonneg hk₀ δ s)

theorem spectralConvolution_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    Integrable (fun s : ℝ => weightedSpectralKernel k hk₀ hk δ s (F (t - s))) := by
  apply ((spectralMajorant_integral hk₀ hδ).1.mul_const ‖F‖).mono'
  · exact ((weightedSpectralKernel_continuous k hk₀ hk δ).clm_apply
      (F.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact Eventually.of_forall (spectral_integrand_bound k hk₀ hk δ F t)

theorem spectralConvolution_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) :
    ‖spectralConvolution k hk₀ hk δ F t‖ ≤ ‖F‖ / (k₀ ^ 2 - δ ^ 2) := by
  have h := norm_integral_le_of_norm_le ((spectralMajorant_integral hk₀ hδ).1.mul_const ‖F‖)
    (Eventually.of_forall (spectral_integrand_bound k hk₀ hk δ F t))
  rw [integral_mul_const, (spectralMajorant_integral hk₀ hδ).2] at h
  simpa only [spectralConvolution, one_div, div_eq_mul_inv, one_mul, mul_comm ‖F‖] using h

theorem spectralConvolution_continuous {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) :
    Continuous (spectralConvolution k hk₀ hk δ F) := by
  have hb : BddAbove (range (fun t : ℝ => ‖F t‖)) :=
    ⟨‖F‖, fun _ ⟨t, ht⟩ => ht ▸ F.norm_coe_le_norm t⟩
  exact hb.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.apply ℝ (SpectralSpace ι)).flip
    (weightedSpectralKernel_integrable k hk₀ hk hδ) F.continuous

theorem spectral_gap_positive {k₀ δ : ℝ} (_hk₀ : 0 < k₀) (hδ : |δ| < k₀) :
    0 < k₀ ^ 2 - δ ^ 2 := by
  have h := abs_lt.mp hδ
  have hp : 0 < (k₀ - δ) * (k₀ + δ) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- The actual convolution bundled in the complete bounded-continuous space. -/
def spectralResolvent {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) : ℝ →ᵇ SpectralSpace ι :=
  BoundedContinuousFunction.ofNormedAddCommGroup (spectralConvolution k hk₀ hk δ F)
    (spectralConvolution_continuous k hk₀ hk hδ F) (‖F‖ / (k₀ ^ 2 - δ ^ 2))
    (spectralConvolution_norm_le k hk₀ hk hδ F)

theorem spectralResolvent_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) :
    ‖spectralResolvent k hk₀ hk hδ F‖ ≤ ‖F‖ / (k₀ ^ 2 - δ ^ 2) := by
  apply (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg _) (spectral_gap_positive hk₀ hδ).le)).mpr
  exact spectralConvolution_norm_le k hk₀ hk hδ F

theorem spectralResolvent_add {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F H : ℝ →ᵇ SpectralSpace ι) :
    spectralResolvent k hk₀ hk hδ (F + H) =
      spectralResolvent k hk₀ hk hδ F + spectralResolvent k hk₀ hk hδ H := by
  apply BoundedContinuousFunction.ext
  intro t
  change (∫ s, weightedSpectralKernel k hk₀ hk δ s (F (t - s) + H (t - s))) = _
  simp_rw [map_add]
  exact integral_add (spectralConvolution_integrable k hk₀ hk hδ F t)
    (spectralConvolution_integrable k hk₀ hk hδ H t)

theorem spectralResolvent_smul {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (c : ℝ) (F : ℝ →ᵇ SpectralSpace ι) :
    spectralResolvent k hk₀ hk hδ (c • F) = c • spectralResolvent k hk₀ hk hδ F := by
  apply BoundedContinuousFunction.ext
  intro t
  change (∫ s, weightedSpectralKernel k hk₀ hk δ s (c • F (t - s))) = _
  simp_rw [map_smul]
  exact integral_smul c _

/-- A true bounded linear map on the time-uniform Hilbert-valued source space. -/
def spectralResolventCLM {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀) :
    (ℝ →ᵇ SpectralSpace ι) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  ({ toFun := spectralResolvent k hk₀ hk hδ
     map_add' := spectralResolvent_add k hk₀ hk hδ
     map_smul' := spectralResolvent_smul k hk₀ hk hδ } :
    (ℝ →ᵇ SpectralSpace ι) →ₗ[ℝ] (ℝ →ᵇ SpectralSpace ι)).mkContinuous
      (k₀ ^ 2 - δ ^ 2)⁻¹ (fun F => by
        change ‖spectralResolvent k hk₀ hk hδ F‖ ≤ (k₀ ^ 2 - δ ^ 2)⁻¹ * ‖F‖
        simpa only [div_eq_mul_inv, mul_comm ‖F‖] using spectralResolvent_norm_le k hk₀ hk hδ F)

theorem spectralResolventCLM_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀) :
    ‖spectralResolventCLM k hk₀ hk hδ‖ ≤ (k₀ ^ 2 - δ ^ 2)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (spectral_gap_positive hk₀ hδ).le)
  intro F
  change ‖spectralResolvent k hk₀ hk hδ F‖ ≤ (k₀ ^ 2 - δ ^ 2)⁻¹ * ‖F‖
  simpa only [div_eq_mul_inv, mul_comm ‖F‖] using spectralResolvent_norm_le k hk₀ hk hδ F

end Yamabe3.Analysis.Delaunay
