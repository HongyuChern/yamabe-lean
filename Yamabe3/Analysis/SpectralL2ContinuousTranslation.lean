import Yamabe3.Analysis.SpectralL2Translation

/-! The canonical continuous solution, including every time evaluation,
is the translate of the very same L2 solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

 theorem spectralL2PotentialContinuous_translate {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i) (hδ : |δ|<k₀) (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s*|V (t-s)|)≤κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s*|V (t-s)|)≤κ)
    (a : ℝ) (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2PotentialContinuousCLM k hk₀ hk hδ (boundedTimeTranslate ℝ a V)
      (l2TimeTranslateCLM (SpectralSpace ι) a F)=
      boundedTimeTranslate (SpectralSpace ι) a (spectralL2PotentialContinuousCLM k hk₀ hk hδ V F) := by
  apply BoundedContinuousFunction.ext
  intro t
  have hS := spectralL2PotentialContinuous_coe_ae k hk₀ hk hδ hκ0 hκ1 (boundedTimeTranslate ℝ a V)
    (translated_kernel_bound V hminus a) (translated_kernel_bound V hplus a) (l2TimeTranslateCLM (SpectralSpace ι) a F)
  rw [← spectralL2IntegralPotentialInverse_translate k hk₀ hk hδ hκ0 hκ1 V hminus hplus a F] at hS
  have hT := l2TimeTranslate_ae (SpectralSpace ι) a (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)
  have hC := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq
    (spectralL2PotentialContinuous_coe_ae k hk₀ hk hδ hκ0 hκ1 V hminus hplus F)
  have he := hS.trans (hT.trans hC.symm)
  have hp := Measure.eq_of_ae_eq he
    (spectralL2PotentialContinuousCLM k hk₀ hk hδ (boundedTimeTranslate ℝ a V)
      (l2TimeTranslateCLM (SpectralSpace ι) a F)).continuous
    ((spectralL2PotentialContinuousCLM k hk₀ hk hδ V F).continuous.comp (continuous_id.add continuous_const))
  exact congrFun hp t

#print axioms spectralL2PotentialContinuous_translate
end Yamabe3.Analysis.Delaunay
