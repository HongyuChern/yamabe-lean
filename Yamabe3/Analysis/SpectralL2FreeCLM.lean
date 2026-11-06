import Yamabe3.Analysis.SpectralL2AlmostEverywhere

/-! An actual bounded linear diagonal resolvent on the full L2 time
space, and agreement with the original bounded-continuous construction
on their common domain. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Resolvent_add {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F G : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2Resolvent k hk₀ hk hδ (F+G)=
      spectralL2Resolvent k hk₀ hk hδ F+spectralL2Resolvent k hk₀ hk hδ G := by
  apply Lp.ext
  have hs := spectralL2Resolvent_coe_ae k hk₀ hk hδ (F+G)
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ (Lp.coeFn_add F G)] at hs
  filter_upwards [hs,spectralL2Resolvent_coe_ae k hk₀ hk hδ F,
    spectralL2Resolvent_coe_ae k hk₀ hk hδ G,
    Lp.coeFn_add (spectralL2Resolvent k hk₀ hk hδ F) (spectralL2Resolvent k hk₀ hk hδ G),
    spectralL2Convolution_add_ae k hk₀ hk hδ F G (Lp.memLp F) (Lp.memLp G)] with t hs hf hg ho ha
  simpa only [Pi.add_apply,hs,hf,hg,ho] using ha

theorem spectralL2Resolvent_smul {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (c : ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2Resolvent k hk₀ hk hδ (c • F)=c • spectralL2Resolvent k hk₀ hk hδ F := by
  apply Lp.ext
  have hs := spectralL2Resolvent_coe_ae k hk₀ hk hδ (c • F)
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ (Lp.coeFn_smul c F),spectralL2Convolution_smul] at hs
  filter_upwards [hs,spectralL2Resolvent_coe_ae k hk₀ hk hδ F,
    Lp.coeFn_smul c (spectralL2Resolvent k hk₀ hk hδ F)] with t hs hf ho
  simpa only [Pi.smul_apply,hf,ho] using hs

def spectralL2FreeCLM {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  ({toFun := spectralL2Resolvent k hk₀ hk hδ
    map_add' := spectralL2Resolvent_add k hk₀ hk hδ
    map_smul' := spectralL2Resolvent_smul k hk₀ hk hδ} :
      Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ)).mkContinuous
    (1/(k₀^2-δ^2)) (spectralL2Resolvent_norm_le k hk₀ hk hδ)

theorem spectralL2FreeCLM_norm_le {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) :
    ‖spectralL2FreeCLM k hk₀ hk hδ‖ ≤ 1/(k₀^2-δ^2) := by
  exact ContinuousLinearMap.opNorm_le_bound _
    (one_div_nonneg.mpr (spectral_gap_positive hk₀ hδ).le) (spectralL2Resolvent_norm_le k hk₀ hk hδ)

theorem spectralL2FreeCLM_agrees_original {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (hF : MemLp F 2) :
    (spectralL2FreeCLM k hk₀ hk hδ (hF.toLp F) : ℝ → SpectralSpace ι)=ᵐ[volume]
      spectralResolventCLM k hk₀ hk hδ F := by
  have h := spectralL2Resolvent_coe_ae k hk₀ hk hδ (hF.toLp F)
  rw [spectralL2Convolution_congr_ae k hk₀ hk δ hF.coeFn_toLp] at h
  filter_upwards [h] with t ht
  exact ht.trans (spectralL2Convolution_eq_original k hk₀ hk δ F t)

#print axioms spectralL2Resolvent_add
#print axioms spectralL2Resolvent_smul
#print axioms spectralL2FreeCLM_norm_le
#print axioms spectralL2FreeCLM_agrees_original
end Yamabe3.Analysis.Delaunay
