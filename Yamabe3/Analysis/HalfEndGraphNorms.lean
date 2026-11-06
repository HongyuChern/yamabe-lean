import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH2SourceGraph

/-! Explicit instance heads expose the existing inherited submodule norms;
no norm, topology or graph membership condition is changed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
instance halfEndH4Graph_normedAddCommGroup : NormedAddCommGroup HalfEndPhysicalH4Graph :=
  @Submodule.normedAddCommGroup ℝ
    (HalfEndEntranceValue × WeakSobolevJetFamily HalfEndPhysicalSliceIndex halfEndBasicAnnulus 4)
    _ _ _ HalfEndPhysicalH4Graph
instance halfEndH4Graph_normedSpace : NormedSpace ℝ HalfEndPhysicalH4Graph :=
  @Submodule.normedSpace ℝ ℝ _ _ _
    (HalfEndEntranceValue × WeakSobolevJetFamily HalfEndPhysicalSliceIndex halfEndBasicAnnulus 4)
    _ _ _ _ HalfEndPhysicalH4Graph
instance halfEndH2SourceGraph_normedAddCommGroup : NormedAddCommGroup HalfEndPhysicalH2SourceGraph :=
  @Submodule.normedAddCommGroup ℝ
    (HalfEndSourceValue × WeakSobolevJetFamily HalfEndPhysicalSliceIndex halfEndSourceAnnulus 2)
    _ _ _ HalfEndPhysicalH2SourceGraph
instance halfEndH2SourceGraph_normedSpace : NormedSpace ℝ HalfEndPhysicalH2SourceGraph :=
  @Submodule.normedSpace ℝ ℝ _ _ _
    (HalfEndSourceValue × WeakSobolevJetFamily HalfEndPhysicalSliceIndex halfEndSourceAnnulus 2)
    _ _ _ _ HalfEndPhysicalH2SourceGraph
@[simp] theorem halfEndH4Graph_norm_fst_eq (v : HalfEndPhysicalH4Graph) : ‖v.1‖ = ‖v‖ := rfl
@[simp] theorem halfEndH2SourceGraph_norm_fst_eq (v : HalfEndPhysicalH2SourceGraph) : ‖v.1‖ = ‖v‖ := rfl
#print axioms halfEndH4Graph_norm_fst_eq
#print axioms halfEndH2SourceGraph_norm_fst_eq
end Yamabe3.Analysis.UniformElliptic
