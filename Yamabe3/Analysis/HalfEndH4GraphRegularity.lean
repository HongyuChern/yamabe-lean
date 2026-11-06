import Yamabe3.Analysis.WeakH4LocalRepresentative
import Yamabe3.Analysis.NativeWeakDilation
import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH4Graph

/-! Every element of the actual H4 graph has local H4 and its retained
continuous value is C2 throughout the punctured radius-four entrance ball.
No smoothness field is appended to the Banach space. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 4 \ {(0:E)}

theorem halfEndEntranceExtension_continuousOn (v : HalfEndEntranceValue) :
    ContinuousOn (halfEndEntranceExtension v) (closedBall (0:E) 4) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (fun x : closedBall (0:E) 4 => halfEndEntranceExtension v x) = v := by
    funext x
    exact halfEndEntranceExtension_of_mem v x.2
  change Continuous (fun x : closedBall (0:E) 4 => halfEndEntranceExtension v x)
  rw [he]
  exact v.continuous

theorem halfEndPhysicalH4Graph_local_H4 (v : HalfEndPhysicalH4Graph) :
    MemWkpLocally 4 (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) O := by
  intro x hx
  have hx0 : x ≠ 0 := hx.2
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hx4 : ‖x‖ < 4 := by simpa only [mem_ball,dist_zero_right] using hx.1
  let r : ℝ := min ‖x‖ 2
  have hr : 0 < r := lt_min hxn (by norm_num)
  have hr2 : r ≤ 2 := min_le_right _ _
  let s : ℝ := -Real.log r
  have hs : -Real.log 2 ≤ s := neg_le_neg (Real.log_le_log hr hr2)
  let i : HalfEndPhysicalSliceIndex := ⟨s,hs⟩
  let c := Real.exp s
  have hc : 0 < c := Real.exp_pos s
  have hcr : c = r⁻¹ := by dsimp only [c,s];rw [Real.exp_neg,Real.exp_log hr]
  have hn : (1/2:ℝ) < ‖c • x‖ ∧ ‖c • x‖ < 2 := by
    rw [norm_smul,Real.norm_of_nonneg hc.le,hcr]
    by_cases hx2 : ‖x‖ ≤ 2
    · have he : r = ‖x‖ := min_eq_left hx2
      rw [he,inv_mul_cancel₀ hxn.ne']
      norm_num
    · have he : r = 2 := min_eq_right (le_of_not_ge hx2)
      rw [he]
      constructor <;> nlinarith [lt_of_not_ge hx2]
  let W := (fun y : E => c • y) ⁻¹' halfEndBasicAnnulus
  have hW : IsOpen W := halfEndBasicAnnulus_isOpen.preimage (continuous_id.const_smul c)
  let q := halfEndWeightedPhysicalSliceMap v.1.1 i
  have hq : MemWkp 4 2 (fun y : E => q (c • y)) W :=
    memWkp_comp_dilation hc.ne' halfEndBasicAnnulus_isOpen (by norm_num) 4 (v.2 i).1
  have he : (fun y : E => (Real.exp (3*s/2))⁻¹*q (c • y)) =
      halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) := by
    funext y
    have hx : Real.exp (-s)*c = 1 := by dsimp only [c];rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    change (Real.exp (3*s/2))⁻¹*(Real.exp (3*s/2)*halfEndEntranceExtension v.1.1 (Real.exp (-s) • (c • y))) = _
    rw [smul_smul,hx,one_smul,← mul_assoc,inv_mul_cancel₀ (Real.exp_pos _).ne',one_mul]
    rfl
  have hu := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hW hq (Real.exp (3*s/2))⁻¹
  rw [he] at hu
  exact ⟨W ∩ O,hW.inter (isOpen_ball.sdiff isClosed_singleton),⟨hn,hx⟩,inter_subset_right,
    hu.mono_set (by norm_num) (hW.inter (isOpen_ball.sdiff isClosed_singleton)) inter_subset_left⟩

theorem halfEndPhysicalH4Graph_contDiffOn_two (v : HalfEndPhysicalH4Graph) :
    ContDiffOn ℝ 2 (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) O := by
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨F,hF,hae⟩ := exists_local_weak_H4_C2_representative hO (halfEndPhysicalH4Graph_local_H4 v)
  have hu : ContinuousOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) O :=
    (halfEndEntranceExtension_continuousOn _).mono (inter_subset_left.trans ball_subset_closedBall)
  have he := Measure.eqOn_open_of_ae_eq (μ := volume) hae hO hF.continuousOn hu
  exact hF.congr (fun x hx => (he hx).symm)

#print axioms halfEndEntranceExtension_continuousOn
#print axioms halfEndPhysicalH4Graph_local_H4
#print axioms halfEndPhysicalH4Graph_contDiffOn_two
end Yamabe3.Analysis.UniformElliptic
