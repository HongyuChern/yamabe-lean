import Yamabe3.Analysis.NativePotentialErrorRows
import Yamabe3.Analysis.NativePrincipalErrorContinuity

/-! The same potential-error expression is continuous on the entrance
collar and linear in the actual retained graph representative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem nativeNormalizedPotentialError_entrance_continuous
    (g : RiemannianMetric 3 E) (ε : ℝ) {κ : ℝ} (p : DelaunayPhaseData κ)
    (v : HalfEndPhysicalH4Graph) :
    Continuous (fun x : HalfEndSourceEntrance => nativeNormalizedPotentialError g ε p.orbit p.phase
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x) := by
  let W : Set E := ball (0:E) 4 \ {(0:E)}
  have hu := (halfEndPhysicalH4Graph_contDiffOn_two v).continuousOn
  have hc : ContinuousOn (nativeDelaunayPotentialError g ε p.orbit p.phase) W := by
    intro x hx
    exact (contDiffAt_nativeDelaunayPotentialError g ε p.smooth p.phase hx.2).continuousAt.continuousWithinAt
  have hρ : ContinuousOn (fun x : E => radialScale ‖x‖) W := by
    unfold radialScale
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div_const
    apply ContinuousOn.neg
    exact continuous_norm.continuousOn.log (fun x hx => norm_ne_zero_iff.mpr hx.2)
  have h := (hc.mul hu).div hρ (fun x _ => (radialScale_pos ‖x‖).ne')
  apply h.comp_continuous continuous_subtype_val
  intro x
  exact ⟨by simpa only [mem_ball,dist_zero_right] using lt_of_le_of_lt x.2.2 (by norm_num : (3:ℝ)<4), x.2.1⟩

theorem nativeNormalizedPotentialError_graph_add (g : RiemannianMetric 3 E) (ε : ℝ)
    {κ : ℝ} (p : DelaunayPhaseData κ)
    (v w : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance) :
    nativeNormalizedPotentialError g ε p.orbit p.phase (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (v+w))) x =
      nativeNormalizedPotentialError g ε p.orbit p.phase (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x+
        nativeNormalizedPotentialError g ε p.orbit p.phase (halfEndEntranceExtension (halfEndPhysicalH4GraphValue w)) x := by
  unfold nativeNormalizedPotentialError
  rw [map_add,halfEndEntranceExtension_add]
  ring

theorem nativeNormalizedPotentialError_graph_smul (g : RiemannianMetric 3 E) (ε c : ℝ)
    {κ : ℝ} (p : DelaunayPhaseData κ)
    (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance) :
    nativeNormalizedPotentialError g ε p.orbit p.phase (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (c • v))) x =
      c*nativeNormalizedPotentialError g ε p.orbit p.phase (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x := by
  unfold nativeNormalizedPotentialError
  rw [map_smul,halfEndEntranceExtension_smul]
  ring

#print axioms nativeNormalizedPotentialError_entrance_continuous
#print axioms nativeNormalizedPotentialError_graph_add
#print axioms nativeNormalizedPotentialError_graph_smul
end Yamabe3.Analysis.UniformElliptic
