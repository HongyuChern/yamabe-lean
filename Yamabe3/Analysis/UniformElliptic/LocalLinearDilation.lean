import Yamabe3.Analysis.UniformElliptic.LocalUniformJet

/-! A fixed spatial half-dilation retains smoothness and has no cost
on derivative orders 0..2. This is a local theorem with a proved compact
extension, not a global smoothness assumption on the selected field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def halfDilatedLinear (P : X →ₗ[ℝ] (E3→ℝ)) : X →ₗ[ℝ] (E3→ℝ) where
  toFun W x := P W ((1/2:ℝ) • x)
  map_add' W Z := by funext x;rw [map_add];rfl
  map_smul' c W := by funext x;rw [map_smul];rfl

theorem halfDilatedLinear_smooth (P : X →ₗ[ℝ] (E3→ℝ))
    (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 3)) (W : X) :
    ContDiffOn ℝ ∞ (halfDilatedLinear P W) (ball (0:E3) 5) := by
  apply (hP W).comp (contDiff_id.const_smul (1/2:ℝ)).contDiffOn
  intro x hx
  rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ)≤1/2)]
  have hn : ‖x‖<5 := by simpa only [mem_ball_zero_iff] using hx
  change (1/2:ℝ)*‖x‖<3
  linarith

theorem halfDilatedLinear_two_jet_bound (P : X →ₗ[ℝ] (E3→ℝ))
    (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 3))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀W,∀j≤2,∀x∈closedBall (0:E3) 2,‖iteratedFDeriv ℝ j (P W) x‖≤C*‖W‖) :
    ∀W,∀j≤2,∀x∈closedBall (0:E3) 4,
      ‖iteratedFDeriv ℝ j (halfDilatedLinear P W) x‖≤C*‖W‖ := by
  intro W j hj x hx
  have hy : (1/2:ℝ) • x∈closedBall (0:E3) 2 := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ)≤1/2)]
    have hn : ‖x‖≤4 := by simpa only [mem_closedBall,dist_zero_right] using hx
    linarith
  obtain ⟨v,hv,_,hve⟩ := exists_smooth_compact_extension_near_compact isOpen_ball
    (isCompact_closedBall (0:E3) 2) (closedBall_subset_ball (by norm_num)) (hP W)
  have he : halfDilatedLinear P W =ᶠ[𝓝 x] (fun y => v ((1/2:ℝ) • y)) := by
    have hh := (hve ((1/2:ℝ) • x) hy).comp_tendsto (continuous_id.const_smul (1/2:ℝ)).continuousAt
    filter_upwards [hh] with y hyy
    exact hyy.symm
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds,
    iteratedFDeriv_comp_const_smul (1/2:ℝ) (hv.of_le (by exact_mod_cast le_top)),norm_smul,norm_pow,
    Real.norm_of_nonneg (by norm_num:(0:ℝ)≤1/2),(hve _ hy).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact (mul_le_mul (show (1/2:ℝ)^j≤1 from pow_le_one₀ (by norm_num) (by norm_num))
    (hb W j hj _ hy) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

#print axioms halfDilatedLinear_smooth
#print axioms halfDilatedLinear_two_jet_bound
end Yamabe3.Analysis.UniformElliptic
