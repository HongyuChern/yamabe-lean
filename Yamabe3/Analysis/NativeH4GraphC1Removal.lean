import Yamabe3.Analysis.WeightedH4C1Removal
import Yamabe3.Analysis.NativeH4GraphAllScaleJet

/-! The actual retained H4 graph value, with the same C2 off-zero
representative, is C1 across the origin and has derivative zero there.
This uses every genuine slice bound, not an extra pointwise assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Poincare.Analysis.Sobolev.Euclidean

theorem nativeH4Graph_representative_C1 (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    ContDiff ℝ 1 u.val ∧ HasFDerivAt u.val (0:E→L[ℝ]ℝ) 0 := by
  apply weighted_H4_global_C1 u.property h0 (B:=ENNReal.ofReal ‖v‖) ENNReal.ofReal_ne_top
  intro s hs
  let i:HalfEndPhysicalSliceIndex:=⟨s,hs⟩
  have he:weightedPhysicalDilation s u.val=ᵐ[volume.restrict halfEndBasicAnnulus]
      halfEndWeightedPhysicalSliceMap v.1.1 i := by
    filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
    change Real.exp (3*s/2)*u.val (Real.exp (-s) • x)=
      Real.exp (3*s/2)*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) (Real.exp (-s) • x)
    rw [hu (halfEnd_physical_slice_mem_entrance_ball i hx.2.le)]
  refine ⟨(MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen he).mpr (v.2 i).1,?_⟩
  rw [wkpNorm_congr_ae (k:=4) (by norm_num) halfEndBasicAnnulus_isOpen he]
  exact halfEndWeightedPhysicalSliceMap_norm_le v i

#print axioms nativeH4Graph_representative_C1
end Yamabe3.Analysis.UniformElliptic
