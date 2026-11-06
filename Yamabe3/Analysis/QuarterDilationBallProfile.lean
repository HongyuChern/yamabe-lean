import Yamabe3.Analysis.UniformElliptic.HalfEndAnnularMeasure

/-! A fixed quarter dilation transfers the ACTUAL full Hk L2 profile
from the unit ball to the radius-four ball, with both volume costs paid. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem derivativeProfile_quarter_dilation_ball_le
    {f:E3→ℝ} (hf:ContDiffOn ℝ ∞ f (ball (0:E3) 3)) (k:ℕ) :
    derivativeProfile 2 (ball (0:E3) 4) k (fun x:E3 => f ((1/4:ℝ) • x))≤
      64*derivativeProfile 2 (ball (0:E3) 1) k f := by
  have hmap {R:ℝ} (hR:0<R) {x:E3} (hx:x∈ball (0:E3) (2*R)) :
      (1/2:ℝ) • x∈ball (0:E3) R := by
    rw [mem_ball_zero_iff,norm_smul]
    have hx':‖x‖<2*R := by simpa only [mem_ball_zero_iff] using hx
    norm_num
    linarith
  let g:E3→ℝ := fun x => f ((1/2:ℝ) • x)
  have hg:ContDiffOn ℝ ∞ g (ball (0:E3) 5) := by
    apply hf.comp (contDiff_id.const_smul (1/2:ℝ)).contDiffOn
    intro x hx
    exact hmap (by norm_num:(0:ℝ)<3) ((ball_subset_ball (by norm_num:(5:ℝ)≤2*3)) hx)
  have h1:=derivativeProfile_scalar_half_dilation_le isOpen_ball measurableSet_ball
    (ball_subset_ball (by norm_num:(1:ℝ)≤3)) hf k (by norm_num:|(1:ℝ)|≤1)
    (fun x hx => hmap (by norm_num:(0:ℝ)<1) hx)
  have h2:=derivativeProfile_scalar_half_dilation_le isOpen_ball measurableSet_ball
    (ball_subset_ball (by norm_num:(2:ℝ)≤5)) hg k (by norm_num:|(1:ℝ)|≤1)
    (fun x hx => hmap (by norm_num:(0:ℝ)<2) hx)
  simp only [one_mul] at h1 h2
  have he:(fun x:E3 => g ((1/2:ℝ) • x))=(fun x:E3 => f ((1/4:ℝ) • x)) := by
    funext x
    dsimp only [g]
    rw [smul_smul]
    norm_num
  rw [he] at h2
  norm_num only [show (2:ℝ)*1=2 by norm_num] at h1
  norm_num only [show (2:ℝ)*2=4 by norm_num] at h2
  calc
    _ ≤ 8*(8*derivativeProfile 2 (ball (0:E3) 1) k f) :=
      h2.trans (mul_le_mul_of_nonneg_left h1 zero_le)
    _ = _ := by ring

#print axioms derivativeProfile_quarter_dilation_ball_le
end Yamabe3.Analysis.UniformElliptic
