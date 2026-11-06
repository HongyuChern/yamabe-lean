import Yamabe3.Analysis.L2TimeTranslation

/-! Isometric reflection of the same L2 source, with its representative
and square norm verified. No smoothness or pointwise source is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]

def l2TimeReflectCLM : Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : ℝ => -t) (Measure.measurePreserving_neg volume)).toContinuousLinearMap

theorem l2TimeReflect_ae (F : Lp H 2 (volume : Measure ℝ)) :
    (l2TimeReflectCLM H F : ℝ→H)=ᵐ[volume] (fun t => F (-t)) :=
  Lp.coeFn_compMeasurePreserving F (Measure.measurePreserving_neg volume)

theorem l2TimeReflect_norm (F : Lp H 2 (volume : Measure ℝ)) :
    ‖l2TimeReflectCLM H F‖=‖F‖ := Lp.norm_compMeasurePreserving F (Measure.measurePreserving_neg volume)

theorem l2TimeReflect_involution (F : Lp H 2 (volume : Measure ℝ)) :
    l2TimeReflectCLM H (l2TimeReflectCLM H F)=F := by
  apply Lp.ext
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae (l2TimeReflect_ae H F)
  filter_upwards [l2TimeReflect_ae H (l2TimeReflectCLM H F),h] with t ht hr
  rw [ht,hr,neg_neg]

#print axioms l2TimeReflect_ae
#print axioms l2TimeReflect_norm
#print axioms l2TimeReflect_involution
end Yamabe3.Analysis.Delaunay
