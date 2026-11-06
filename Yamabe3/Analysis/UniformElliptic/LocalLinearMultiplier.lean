import Yamabe3.Analysis.UniformElliptic.RegularFieldSourceGraphCost
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! A fixed smooth physical coefficient multiplies the same field.
The actual second-order Leibniz cost is paid before constructing the
weighted source graph; no new regularity of the input is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal BigOperators
namespace Yamabe3.Analysis.UniformElliptic
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def localCoefficientLinear (q : E3→ℝ) (P : X →ₗ[ℝ] (E3→ℝ)) : X →ₗ[ℝ] (E3→ℝ) where
  toFun W x := q x*P W x
  map_add' W Z := by funext x;simp only [map_add,Pi.add_apply,mul_add]
  map_smul' c W := by funext x;simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring

theorem localCoefficientLinear_two_jet_bound
    (q : E3→ℝ) (hq : ContDiffOn ℝ ∞ q (ball (0:E3) 5))
    (D : ℝ) (hD : 0≤D) (hqb : ∀j≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ j q x‖≤D)
    (P : X →ₗ[ℝ] (E3→ℝ)) (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 5))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀W,∀j≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ j (P W) x‖≤C*‖W‖) :
    ∀W,∀j≤2,∀x∈closedBall (0:E3) 4,
      ‖iteratedFDeriv ℝ j (localCoefficientLinear q P W) x‖≤(4*D*C)*‖W‖ := by
  intro W j hj x hx
  obtain ⟨v,hv,_,hve⟩ := exists_smooth_compact_extension_near_compact isOpen_ball
    (isCompact_closedBall (0:E3) 4) (closedBall_subset_ball (by norm_num)) (hP W)
  obtain ⟨r,hr,_,hre⟩ := exists_smooth_compact_extension_near_compact isOpen_ball
    (isCompact_closedBall (0:E3) 4) (closedBall_subset_ball (by norm_num)) hq
  have he : localCoefficientLinear q P W =ᶠ[𝓝 x] (fun y => r y*v y) := by
    filter_upwards [hve x hx,hre x hx] with y hyv hyr
    change q y*P W y=r y*v y
    rw [hyv,hyr]
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
  apply (norm_iteratedFDeriv_mul_le hr hv x (by exact_mod_cast le_top)).trans
  calc
    _ ≤ ∑ i∈Finset.range (j+1),(j.choose i:ℝ)*D*(C*‖W‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [(hre x hx).iteratedFDeriv ℝ i |>.self_of_nhds,
        (hve x hx).iteratedFDeriv ℝ (j-i) |>.self_of_nhds]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hqb i (hi'.trans hj) x hx) (Nat.cast_nonneg _))
        (hb W (j-i) (Nat.sub_le j i |>.trans hj) x hx) (norm_nonneg _) (by positivity)
    _ = (∑i∈Finset.range (j+1),(j.choose i:ℝ))*D*(C*‖W‖) := by rw [Finset.sum_mul,Finset.sum_mul]
    _ ≤ 4*D*(C*‖W‖) := by
      have hh : (∑i∈Finset.range (j+1),(j.choose i:ℝ))≤4 := by
        have hid : (∑i∈Finset.range (j+1),(j.choose i:ℝ))=(2:ℝ)^j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hid]
        exact (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) hj).trans_eq (by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hD) (mul_nonneg hC (norm_nonneg W))
    _ = _ := by ring

theorem exists_regularField_coefficient_source_graph
    (q : E3→ℝ) (hq : ContDiffOn ℝ ∞ q (ball (0:E3) 5))
    (D : ℝ) (hD : 0≤D) (hqb : ∀j≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ j q x‖≤D)
    (P : X →ₗ[ℝ] (E3→ℝ)) (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 5))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀W,∀j≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ j (P W) x‖≤C*‖W‖) :
    ∃T : X →L[ℝ] HalfEndPhysicalH2SourceGraph,
      ‖T‖≤regularFieldSourceGraphCost*(4*D*C) ∧ ∀W,∀y : HalfEndSourceEntrance,
        halfEndPhysicalH2SourceGraphValue (T W) y=(Delaunay.radialScale ‖(y:E3)‖)⁻¹*(q y*P W y) :=
  exists_regularField_source_graph_with_cost (localCoefficientLinear q P) (fun W => hq.mul (hP W))
    (4*D*C) (by positivity) (localCoefficientLinear_two_jet_bound q hq D hD hqb P hP C hC hb)

#print axioms localCoefficientLinear_two_jet_bound
#print axioms exists_regularField_coefficient_source_graph
end Yamabe3.Analysis.UniformElliptic
