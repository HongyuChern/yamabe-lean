import Yamabe3.Analysis.NativeSingularPowerIntegrability

/-! In dimension three the actual inverse-square-root bound at one pole
and continuity elsewhere yield local integrability, with no assigned
value at the pole affecting the result. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem locallyIntegrable_of_offZero_inv_sqrt_bound {F:E→ℝ}
    (hc:ContinuousOn F ({(0:E)}ᶜ)) {C:ℝ}
    (hb:∀x:E,x≠0 → ‖x‖ ≤ 1 → ‖F x‖ ≤ C/Real.sqrt ‖x‖) :
    LocallyIntegrable F volume := by
  have hm:Measurable F:=hc.measurable_of_countable_compl (by
    simpa only [compl_compl] using countable_singleton (0:E))
  have hball:IntegrableOn F (ball (0:E) 1) volume:=by
    apply integrableOn_ball_of_norm_le_rpow (α:=(1/2:ℝ)) (by simp) (by norm_num)
      (C:=C) ?_ hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0:E))] with x hx hx0
    have hn:‖x‖ ≤ 1:=(by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<1).le
    simpa only [Real.rpow_neg (norm_nonneg x),Real.sqrt_eq_rpow,div_eq_mul_inv] using hb x hx0 hn
  intro x
  by_cases hx:x=0
  · subst x
    exact ⟨ball (0:E) 1,Metric.ball_mem_nhds _ zero_lt_one,hball⟩
  · have hi:=hc.integrableAt_nhdsWithin (μ:=volume) isClosed_singleton.isOpen_compl.measurableSet hx
    rwa [nhdsWithin_eq_nhds.mpr (isClosed_singleton.isOpen_compl.mem_nhds hx)] at hi

#print axioms locallyIntegrable_of_offZero_inv_sqrt_bound
end Yamabe3.Analysis.UniformElliptic
