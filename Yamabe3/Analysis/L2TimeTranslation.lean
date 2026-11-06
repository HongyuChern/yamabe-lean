import Yamabe3.Analysis.SpectralL2PotentialContinuous

/-! Actual isometric time translation on the original source space. The
shifted representative and shifted potential are explicit, with no new
source choice or time-dependent norm loss. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]

def l2TimeTranslateCLM (a : ℝ) : Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : ℝ => t+a) (measurePreserving_add_right volume a)).toContinuousLinearMap

 theorem l2TimeTranslate_ae (a : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    (l2TimeTranslateCLM H a F : ℝ → H)=ᵐ[volume] (fun t => F (t+a)) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right volume a)

 theorem l2TimeTranslate_norm (a : ℝ) (F : Lp H 2 (volume : Measure ℝ)) :
    ‖l2TimeTranslateCLM H a F‖=‖F‖ := Lp.norm_compMeasurePreserving F (measurePreserving_add_right volume a)

 theorem l2TimeTranslate_toLp (a : ℝ) (F : ℝ → H) (hF : MemLp F 2) :
    l2TimeTranslateCLM H a (hF.toLp F)=
      (hF.comp_measurePreserving (measurePreserving_add_right volume a)).toLp (fun t => F (t+a)) := rfl

 def boundedTimeTranslate (a : ℝ) (F : ℝ →ᵇ H) : ℝ →ᵇ H :=
  F.compContinuous ⟨fun t : ℝ => t+a,continuous_id.add continuous_const⟩

 theorem boundedTimeTranslate_norm (a : ℝ) (F : ℝ →ᵇ H) : ‖boundedTimeTranslate H a F‖=‖F‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    intro t
    exact F.norm_coe_le_norm (t+a)
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (boundedTimeTranslate H a F))).mpr
    intro t
    simpa only [boundedTimeTranslate,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,sub_add_cancel] using
      (boundedTimeTranslate H a F).norm_coe_le_norm (t-a)

 theorem translated_kernel_bound {k₀ δ κ : ℝ} (V : ℝ →ᵇ ℝ)
    (hV : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s*|V (t-s)|)≤κ) (a : ℝ) :
    ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s*|boundedTimeTranslate ℝ a V (t-s)|)≤κ := by
  intro t
  have h := hV (t+a)
  simpa only [boundedTimeTranslate,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
    sub_add_eq_add_sub] using h

#print axioms l2TimeTranslate_ae
#print axioms l2TimeTranslate_norm
#print axioms l2TimeTranslate_toLp
#print axioms boundedTimeTranslate_norm
#print axioms translated_kernel_bound
end Yamabe3.Analysis.Delaunay
