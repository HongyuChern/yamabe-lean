import Yamabe3.Analysis.NativeRegularLowH4Identity
import Yamabe3.Analysis.WeightedH4C1Removal
import PoincareLib.Geometry.Manifold.PartitionOfUnity.CompactSupport

/-! Every original weighted H4 graph has a compact C1 realization of
the SAME retained field on the inner ball. No independent representative
or derivative at the puncture is an input. The cutoff is fixed before
the graph element, so the actual realized family is linear. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_H4_core_cutoff :
    ∃χ:E3→ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆ball (0:E3) 3 ∧
      ∀x∈closedBall (0:E3) 2,χ=ᶠ[𝓝 x] (fun _:E3 => (1:ℝ)) := by
  have hKO:closedBall (0:E3) 2⊆ball (0:E3) 3 := closedBall_subset_ball (by norm_num)
  obtain ⟨χ,hχ,hc,hs,_,h1⟩ := PoincareMT.exists_contMDiff_cutoff_of_isCompact
    (n:=3) (isCompact_closedBall (0:E3) 2) isOpen_ball hKO
  exact ⟨χ,hχ.contDiff,hc,hs,h1⟩

def H4CoreCutoffLinear (χ:E3→ℝ) : HalfEndPhysicalH4Graph →ₗ[ℝ] (E3→ℝ) where
  toFun v x := χ x*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) x
  map_add' v w := by funext x; simp only [map_add,halfEndEntranceExtension_add,Pi.add_apply,mul_add]
  map_smul' c v := by
    funext x
    change χ x*halfEndEntranceExtension (halfEndPhysicalH4GraphValue (c • v)) x=
      c*(χ x*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) x)
    rw [halfEndPhysicalH4GraphValue.map_smul,halfEndEntranceExtension_smul]
    ring

theorem H4CoreCutoffLinear_eval_continuous (χ:E3→ℝ) (x:E3) :
    Continuous (fun v:HalfEndPhysicalH4Graph => H4CoreCutoffLinear χ v x) :=
  continuous_const.mul ((halfEndEntranceEval x).continuous.comp halfEndPhysicalH4GraphValue.continuous)

theorem H4CoreCutoffLinear_C1
    {χ:E3→ℝ} (hχ:ContDiff ℝ ∞ χ) (hs:tsupport χ⊆ball (0:E3) 3)
    (h1:∀x∈closedBall (0:E3) 2,χ=ᶠ[𝓝 x] (fun _:E3 => (1:ℝ)))
    (v:HalfEndPhysicalH4Graph) : ContDiff ℝ 1 (H4CoreCutoffLinear χ v) := by
  let f := halfEndPhysicalH4GraphValue v
  let F := H4CoreCutoffLinear χ v
  have hF2:ContDiffOn ℝ 2 F ({(0:E3)}ᶜ:Set E3) := by
    intro x hx
    by_cases hxχ:x∈tsupport χ
    · have hx4:x∈ball (0:E3) 4\{(0:E3)} :=
        ⟨(ball_subset_ball (by norm_num)) (hs hxχ),hx⟩
      exact (((hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt).mul
        ((halfEndPhysicalH4Graph_contDiffOn_two v).contDiffAt
          ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hx4))).contDiffWithinAt
    · have he:F=ᶠ[𝓝 x] (fun _:E3 => (0:ℝ)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ] with y hy
        change χ y*halfEndEntranceExtension f y=0
        rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
  have h0:F 0=0 := by
    change χ 0*halfEndEntranceExtension f 0=0
    rw [(halfEndH4Graph_origin_jet v).1,mul_zero]
  obtain ⟨u,hu⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_closedBall:IsClosed (closedBall (0:E3) 4)) f
  have heq {x:E3} (hx:x∈closedBall (0:E3) 4) :
      u x=halfEndEntranceExtension f x := by
    rw [halfEndEntranceExtension_of_mem f hx]
    exact congrArg (fun H:C(HalfEndEntranceBall,ℝ) => H ⟨x,hx⟩) hu
  have hall (s:ℝ) (hs : -Real.log 2 ≤ s) : MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤ENNReal.ofReal ‖v‖ := by
    let i:HalfEndPhysicalSliceIndex := ⟨s,hs⟩
    have hae:weightedPhysicalDilation s u=ᵐ[volume.restrict halfEndBasicAnnulus]
        halfEndWeightedPhysicalSliceMap v.val.1 i := by
      filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
      change Real.exp (3*s/2)*u (Real.exp (-s) • x)=
        Real.exp (3*s/2)*halfEndEntranceExtension f (Real.exp (-s) • x)
      rw [heq (halfEnd_physical_slice_mem_entrance_ball i hx.2.le)]
    refine ⟨(MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen hae).mpr (v.2 i).1,?_⟩
    rw [wkpNorm_congr_ae (k:=4) (by norm_num) halfEndBasicAnnulus_isOpen hae]
    exact halfEndWeightedPhysicalSliceMap_norm_le v i
  obtain ⟨D,hD,hb⟩ := exists_weighted_H4_first_jet_decay_constant
  have hdec := hb u u.continuous.continuousOn (ENNReal.ofReal ‖v‖) ENNReal.ofReal_ne_top hall
  apply (C1_removal_of_sqrt_first_jet_decay (M:=D*(ENNReal.ofReal ‖v‖).toReal) hF2 h0
    (mul_nonneg hD ENNReal.toReal_nonneg) ?_).1
  intro x hx hx1
  have hx2:x∈closedBall (0:E3) 2 := by rw [mem_closedBall,dist_zero_right]; linarith
  have hx4:x∈ball (0:E3) 4 := by rw [mem_ball_zero_iff]; linarith
  have hg:F=ᶠ[𝓝 x] u := by
    filter_upwards [h1 x hx2,isOpen_ball.mem_nhds hx4] with y hy hy4
    change χ y*halfEndEntranceExtension f y=u y
    rw [hy,one_mul,←heq (ball_subset_closedBall hy4)]
  simpa only [hg.self_of_nhds,hg.fderiv_eq] using hdec x hx hx1

theorem H4CoreCutoffLinear_support {χ:E3→ℝ} (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E3) 3) (v:HalfEndPhysicalH4Graph) :
    HasCompactSupport (H4CoreCutoffLinear χ v) ∧
      tsupport (H4CoreCutoffLinear χ v)⊆ball (0:E3) 3 :=
  ⟨hc.mul_right,tsupport_mul_subset_left.trans hs⟩

#print axioms exists_H4_core_cutoff
#print axioms H4CoreCutoffLinear_eval_continuous
#print axioms H4CoreCutoffLinear_C1
#print axioms H4CoreCutoffLinear_support
end Yamabe3.Analysis.UniformElliptic
