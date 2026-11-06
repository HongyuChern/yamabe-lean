import Yamabe3.Analysis.NativeHalfEndH2SourceSolver

/-! Expose the inherited submodule norm on the actual high-source kernel.
The source graph and its topology are unchanged. No substitute norm or
new source regularity hypothesis is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic

instance halfEndHighH2Source_normedAddCommGroup : NormedAddCommGroup HalfEndHighH2Source :=
  @Submodule.normedAddCommGroup ℝ HalfEndPhysicalH2SourceGraph _ _ _
    halfEndH2HighSourceDefect.ker

instance halfEndHighH2Source_normedSpace : NormedSpace ℝ HalfEndHighH2Source :=
  @Submodule.normedSpace ℝ ℝ _ _ _ HalfEndPhysicalH2SourceGraph _ _ _ _
    halfEndH2HighSourceDefect.ker

@[simp] theorem halfEndHighH2Source_norm_val (f : HalfEndHighH2Source) : ‖f.1‖ = ‖f‖ := rfl

#print axioms halfEndHighH2Source_norm_val
end Yamabe3.Analysis.UniformElliptic
