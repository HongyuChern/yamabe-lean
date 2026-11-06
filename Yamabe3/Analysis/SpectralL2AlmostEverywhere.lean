import Yamabe3.Analysis.SpectralL2Realization

/-! The free L2 convolution is defined on arbitrary L2 representatives.
Its true integrability and linearity are almost-everywhere statements,
independent of a chosen strongly measurable modification. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Convolution_of_memLp {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) :
    (∀ᵐ t : ℝ,Integrable (fun s : ℝ => weightedSpectralKernel k hk₀ hk δ (t-s) (F s))) ∧
      MemLp (spectralL2Convolution k hk₀ hk δ F) 2 := by
  let G := hF.1.mk F
  have hG : StronglyMeasurable G := hF.1.stronglyMeasurable_mk
  have hFG : F=ᵐ[volume]G := hF.1.ae_eq_mk
  have hG2 : MemLp G 2 := hF.ae_eq hFG
  have h := spectralL2Convolution_integrable_memLp k hk₀ hk hδ G hG hG2
  constructor
  · filter_upwards [h.1] with t ht
    apply ht.congr
    filter_upwards [hFG] with s hs
    rw [hs]
  · rw [spectralL2Convolution_congr_ae k hk₀ hk δ hFG]
    exact h.2

theorem spectralL2Convolution_add_ae {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F G : ℝ → SpectralSpace ι) (hF : MemLp F 2) (hG : MemLp G 2) :
    spectralL2Convolution k hk₀ hk δ (F+G)=ᵐ[volume]
      (spectralL2Convolution k hk₀ hk δ F+spectralL2Convolution k hk₀ hk δ G) := by
  filter_upwards [(spectralL2Convolution_of_memLp k hk₀ hk hδ F hF).1,
    (spectralL2Convolution_of_memLp k hk₀ hk hδ G hG).1] with t hf hg
  change (∫ s : ℝ,weightedSpectralKernel k hk₀ hk δ (t-s) (F s+G s))=_
  simp_rw [map_add]
  exact integral_add hf hg

theorem spectralL2Convolution_smul {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (δ c : ℝ) (F : ℝ → SpectralSpace ι) :
    spectralL2Convolution k hk₀ hk δ (c • F)=c • spectralL2Convolution k hk₀ hk δ F := by
  funext t
  change (∫ s : ℝ,weightedSpectralKernel k hk₀ hk δ (t-s) (c • F s))=_
  simp_rw [map_smul]
  exact integral_smul c _

#print axioms spectralL2Convolution_of_memLp
#print axioms spectralL2Convolution_add_ae
#print axioms spectralL2Convolution_smul
end Yamabe3.Analysis.Delaunay
