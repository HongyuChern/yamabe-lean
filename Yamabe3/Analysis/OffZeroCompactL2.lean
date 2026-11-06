import Yamabe3.Analysis.OffZeroLocalIntegrability
import Mathlib.MeasureTheory.Function.L2Space

/-! A genuine inverse-square-root bound at the pole yields local L2,
not only L1. Arbitrary values at the pole do not affect the class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric
open scoped Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem memLp_on_compact_of_offZero_inv_sqrt_bound {F:E→ℝ}
    (hc:ContinuousOn F ({(0:E)}ᶜ)) {C a:ℝ} (ha:0<a)
    (hb:∀x:E,x≠0 → ‖x‖ ≤ a → ‖F x‖ ≤ C/Real.sqrt ‖x‖)
    {K:Set E} (hK:IsCompact K) : MemLp F 2 (volume.restrict K) := by
  have hm:Measurable F:=hc.measurable_of_countable_compl (by
    simpa only [compl_compl] using countable_singleton (0:E))
  have hball:IntegrableOn (fun x=>F x^2) (ball (0:E) a) volume:=by
    apply integrableOn_ball_of_norm_le_rpow (α:=(1:ℝ)) (by simp) (by norm_num)
      (C:=C^2) ?_ (hm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0:E))] with x hx hx0
    have hn:‖x‖ ≤ a:=(by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<a).le
    calc
      ‖F x^2‖ = ‖F x‖^2 := norm_pow _ _
      _ ≤ (C/Real.sqrt ‖x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (hb x hx0 hn) _
      _ = C^2*‖x‖^(-(1:ℝ)) := by rw [div_pow,Real.sq_sqrt (norm_nonneg x),Real.rpow_neg_one];rfl
  have hLI:LocallyIntegrable (fun x=>F x^2) volume:=by
    intro x
    by_cases hx:x=0
    · subst x
      exact ⟨ball (0:E) a,Metric.ball_mem_nhds _ ha,hball⟩
    · have hi:=(hc.pow 2).integrableAt_nhdsWithin (μ:=volume) isClosed_singleton.isOpen_compl.measurableSet hx
      rwa [nhdsWithin_eq_nhds.mpr (isClosed_singleton.isOpen_compl.mem_nhds hx)] at hi
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (hLI.integrableOn_isCompact hK)

theorem continuousOn_compact_memLp_top {K:Set E} (hK:IsCompact K)
    {f:E→ℝ} (hf:ContinuousOn f K) : MemLp f ⊤ (volume.restrict K) := by
  obtain ⟨C,hC⟩:=hK.exists_bound_of_continuousOn hf
  exact memLp_top_of_bound (hf.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx=>hC x hx)

#print axioms memLp_on_compact_of_offZero_inv_sqrt_bound
#print axioms continuousOn_compact_memLp_top
end Yamabe3.Analysis.UniformElliptic
