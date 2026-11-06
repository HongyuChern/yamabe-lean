import Yamabe3.Analysis.NativeLocalC2CauchyGluing
import Yamabe3.Analysis.NativeC1ChartEnergyTrace

/-! A compact C2 lifting is constructed near the actual radius-r sphere
from an off-zero C2 field. Its support lies in the prescribed chart and
its germ, including first derivatives, is unchanged on that sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff Manifold
namespace Yamabe3.Analysis.SpherePolar

theorem exists_compact_C2_supported_extension {O K:Set E} (hO:IsOpen O) (hK:IsCompact K) (hKO:K⊆O)
    {u:E→ℝ} (hu:ContDiffOn ℝ 2 u O) :
    ∃F:E→ℝ,ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ tsupport F⊆O ∧ ∀x∈K,F=ᶠ[𝓝 x]u := by
  obtain ⟨χ,hχ,hχc,hχO,_,hχone⟩:=PoincareMT.exists_contMDiff_cutoff_of_isCompact (n:=3) hK hO hKO
  have hd:ContDiff ℝ 2 χ:=hχ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨fun x=>χ x*u x,?_,hχc.mul_right,(tsupport_mul_subset_left).trans hχO,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx:x∈O
    · exact hd.contDiffAt.mul (hu.contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      have hz:=notMem_tsupport_iff_eventuallyEq.mp (fun ht=>hx (hχO ht))
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [hχone x hx] with y hy
    simpa only [Pi.one_apply,one_mul] using congrArg (fun a:ℝ=>a*u y) hy

theorem exists_scaled_C2_boundary_cutoff {r:ℝ} (hr:0<r)
    {u:E→ℝ} (hu:ContDiffOn ℝ 2 u ({0}ᶜ:Set E)) :
    ∃F:E→ℝ,ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      tsupport F⊆ball (0:E) (3*r)\closedBall (0:E) (r/3) ∧
      ∀θ:S,F=ᶠ[𝓝 (r • (θ:E))] (fun y:E=>u (r⁻¹ • y)) := by
  let O:=ball (0:E) (3*r)\closedBall (0:E) (r/3)
  have hO:IsOpen O:=isOpen_ball.sdiff isClosed_closedBall
  have hSO:sphere (0:E) r⊆O := by
    intro x hx
    have hxnorm:‖x‖=r:=by simpa only [mem_sphere,dist_zero_right] using hx
    constructor
    · rw [mem_ball,dist_zero_right,hxnorm]; linarith
    · rw [mem_closedBall,dist_zero_right,hxnorm]; linarith
  have hscaled:ContDiffOn ℝ 2 (fun y:E=>u (r⁻¹ • y)) O := by
    apply ContDiffOn.comp hu (contDiff_id.const_smul r⁻¹).contDiffOn
    intro y hy
    have hy0:y≠0 := by
      intro hz
      have hmem: y∈closedBall (0:E) (r/3) := by rw [hz]; exact mem_closedBall_self (by positivity)
      exact hy.2 hmem
    exact smul_ne_zero (inv_ne_zero hr.ne') hy0
  obtain ⟨F,hF,hFc,hFs,hnear⟩:=exists_compact_C2_supported_extension hO (isCompact_sphere _ _) hSO hscaled
  refine ⟨F,hF,hFc,hFs,fun θ=>hnear _ ?_⟩
  rw [mem_sphere,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ hr.le]

#print axioms exists_compact_C2_supported_extension
#print axioms exists_scaled_C2_boundary_cutoff
end Yamabe3.Analysis.SpherePolar
