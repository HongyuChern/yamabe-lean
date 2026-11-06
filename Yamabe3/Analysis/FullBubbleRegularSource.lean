import Yamabe3.Analysis.UniformElliptic.LocalLinearMultiplier
import Yamabe3.Analysis.FullBubbleSpatialPotentialJets
import Yamabe3.Analysis.NativeHalfEndSourceRegularity

/-! Actual full-bubble reaction of one regular field in the original
weighted source space, retaining the sign and coefficient eight. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal BigOperators
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fullBubbleSpatialPotential_smooth {r : ℝ} (hr : 0<r) :
    ContDiff ℝ ∞ (fullBubbleSpatialPotential r) := by
  apply contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
  intro x
  exact pow_ne_zero 2 (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_of_pos hr)))

theorem exists_fullBubble_compact_two_jet_bound (τ : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀j≤2,∀x∈closedBall (0:E) 4,
      ‖iteratedFDeriv ℝ j (fullBubbleSpatialPotential (Real.exp τ)) x‖≤D := by
  have hs := fullBubbleSpatialPotential_smooth (Real.exp_pos τ)
  have he (j:Fin 3) : ∃D:ℝ,∀x∈closedBall (0:E) 4,
      ‖iteratedFDeriv ℝ j.1 (fullBubbleSpatialPotential (Real.exp τ)) x‖≤D :=
    (isCompact_closedBall (0:E) 4).exists_bound_of_continuousOn
      (hs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose D hD using he
  let C := ∑j:Fin 3,max 0 (D j)
  have hC : 0≤C := Finset.sum_nonneg (fun j _ => le_max_left _ _)
  refine ⟨C,hC,fun j hj x hx => ?_⟩
  let i : Fin 3 := ⟨j,by omega⟩
  exact ((hD i x hx).trans (le_max_right 0 (D i))).trans
    (Finset.single_le_sum (fun k _ => le_max_left 0 (D k)) (Finset.mem_univ i))

theorem exists_fullBubble_regular_reaction_source (τ : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀(P : X →ₗ[ℝ] (E→ℝ)),
      (∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E) 5)) →
      ∀C : ℝ,0≤C →
      (∀W,∀j≤2,∀x∈closedBall (0:E) 4,‖iteratedFDeriv ℝ j (P W) x‖≤C*‖W‖) →
      ∃T : X →L[ℝ] HalfEndPhysicalH2SourceGraph,‖T‖≤D*C ∧
        ∀W,∀y : HalfEndSourceEntrance,
          halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue (T W)) y=
            8*nativeHalfEndPotentialCoefficient (fullBubblePhasePotential τ) y*P W y := by
  obtain ⟨D,hD,hqb⟩ := exists_fullBubble_compact_two_jet_bound τ
  refine ⟨regularFieldSourceGraphCost*(4*D),mul_nonneg regularFieldSourceGraphCost_nonneg (by positivity),fun P hP C hC hb => ?_⟩
  obtain ⟨T,hT,hTv⟩ := exists_regularField_coefficient_source_graph
    (fullBubbleSpatialPotential (Real.exp τ)) (fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).contDiffOn
    D hD hqb P hP C hC hb
  refine ⟨T,hT.trans_eq (by ring),fun W y => ?_⟩
  rw [halfEndEuclideanPhysicalSource,halfEndSourceExtension_of_mem _ y.2,hTv,
    nativeHalfEnd_fullBubble_spatial_eq τ y.2.1]
  field_simp [(radialScale_pos ‖(y:E)‖).ne']

#print axioms fullBubbleSpatialPotential_smooth
#print axioms exists_fullBubble_compact_two_jet_bound
#print axioms exists_fullBubble_regular_reaction_source
end Yamabe3.Analysis.SpherePolar
