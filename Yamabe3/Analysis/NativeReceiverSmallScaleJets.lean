import Yamabe3.Analysis.H4BallSmallScaleC2
import Yamabe3.Analysis.NativeJacobianChartEquation

/-! The same smooth returning field has uniform entrance-scale two-jets.
The small-to-large radius ratio is 8 exp(s), not an independent field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)
variable {M:Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem exists_nativeReceiver_entrance_two_jet_bound :
    ∃C:ℝ,0<C ∧ ∀(e:OpenPartialHomeomorph E M),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source →
      ∀(a s:ℝ),0<a → s≤Real.log (1/32:ℝ) →
      ball (0:E) (a*Real.exp (-s)/2)⊆e.source →
      ∀U:M→ℝ,ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U (e '' ball (0:E) (a*Real.exp (-s)/2)) →
      ∀n≤2,∀x∈closedBall (0:E) 2,
      ENNReal.ofReal ‖iteratedFDeriv ℝ n (fun y=>U (e (a • y))) x‖≤
        ENNReal.ofReal C*derivativeProfile 2 (ball (0:E) 1) 4
          (fun y=>U (e ((a*Real.exp (-s)/8) • y))) := by
  obtain ⟨C,hC,hb⟩:=exists_H4_ball_smallScale_C2_bound
  refine ⟨C,hC,fun e he a s ha hs hsource U hU n hn x hx=>?_⟩
  let R:=a*Real.exp (-s)/2
  let r:=a*Real.exp (-s)/8
  let q:=8*Real.exp s
  have hpos:0<a*Real.exp (-s):=mul_pos ha (Real.exp_pos _)
  have hr:0<r:=by dsimp only [r];positivity
  have hR:0<R:=by dsimp only [R];positivity
  have h3:r*3<R:=by dsimp only [r,R];linarith only [hpos]
  have hmap:MapsTo (fun y:E=>r • y) (ball (0:E) 3) (ball (0:E) R):=by
    intro y hy
    have hy3:‖y‖<3:=by simpa using hy
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left hy3 hr).trans h3
  have hΩ:IsOpen (e '' ball (0:E) R):=e.isOpen_image_of_subset_source isOpen_ball hsource
  have hu:∀y∈ball (0:E) R,ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) ∞ U (e y):=
    fun y hy=>hU.contMDiffAt (hΩ.mem_nhds (mem_image_of_mem e hy))
  have hus:ContDiffOn ℝ ∞ (fun y:E=>U (e (r • y))) (ball (0:E) 3):=
    (contDiffOn_native_chart_representative e he hsource hu).comp (contDiff_id.const_smul r).contDiffOn hmap
  have hq:q∈Icc (0:ℝ) (1/4):=by
    have he:Real.exp s≤(1/32:ℝ):=(Real.exp_le_exp.mpr hs).trans_eq (Real.exp_log (by norm_num))
    exact ⟨mul_nonneg (by norm_num) (Real.exp_pos _).le,by dsimp only [q];linarith only [he]⟩
  have hcancel:r*q=a:=by
    dsimp only [r,q]
    have he:Real.exp (-s)*Real.exp s=1:=by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
    calc
      _ = a*(Real.exp (-s)*Real.exp s):=by ring
      _ = a:=by rw [he,mul_one]
  have hid:(fun y:E=>U (e (r • (q • y))))=(fun y:E=>U (e (a • y))):=by
    funext y
    rw [smul_smul,hcancel]
  have hh:=hb _ hus q hq n hn x hx
  rw [hid] at hh
  exact ((ENNReal.ofReal_le_ofReal hh).trans_eq (ENNReal.ofReal_mul hC.le)).trans
    (mul_le_mul le_rfl ENNReal.ofReal_toReal_le zero_le zero_le)

#print axioms exists_nativeReceiver_entrance_two_jet_bound
end Yamabe3.Analysis.SpherePolar
