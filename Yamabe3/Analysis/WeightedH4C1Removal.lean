import Yamabe3.Analysis.WeightedH4FirstJetDecay

/-! The all-scale H4 first-jet estimate removes the point at the C1
level for the same zero-valued representative. No new representative
or differentiability hypothesis at the removed point is supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem C1_removal_of_sqrt_first_jet_decay {u:E→ℝ}
    (hu:ContDiffOn ℝ 2 u ({(0:E)}ᶜ)) (h0:u 0=0)
    {M:ℝ} (hM:0 ≤ M)
    (hb:∀x:E,x≠0 → ‖x‖ ≤ 1 →
      ‖u x‖ ≤ M*‖x‖*Real.sqrt ‖x‖ ∧ ‖fderiv ℝ u x‖ ≤ M*Real.sqrt ‖x‖) :
    ContDiff ℝ 1 u ∧ HasFDerivAt u (0:E→L[ℝ]ℝ) 0 := by
  have hs:Tendsto (fun x:E=>M*Real.sqrt ‖x‖) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp (continuous_norm.tendsto (0:E))).const_mul M
  have hv:Tendsto (fun x:E=>‖x‖⁻¹*‖u x‖) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x=>mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _))
      ?_ hs
    filter_upwards [Metric.ball_mem_nhds (0:E) zero_lt_one] with x hx
    have hn:‖x‖ ≤ 1 := (by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < 1).le
    by_cases hx0:x=0
    · simp [hx0]
    · calc
        ‖x‖⁻¹*‖u x‖ ≤ ‖x‖⁻¹*(M*‖x‖*Real.sqrt ‖x‖) :=
          mul_le_mul_of_nonneg_left (hb x hx0 hn).1 (inv_nonneg.mpr (norm_nonneg x))
        _ = M*Real.sqrt ‖x‖ := by field_simp
  have hd0:HasFDerivAt u (0:E→L[ℝ]ℝ) 0 := by
    rw [hasFDerivAt_iff_tendsto]
    simpa only [sub_zero,h0,ContinuousLinearMap.zero_apply] using hv
  have hfd0:fderiv ℝ u 0=0 := hd0.fderiv
  have hdlim:Tendsto (fun x:E=>‖fderiv ℝ u x‖) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x=>norm_nonneg _) ?_ hs
    filter_upwards [Metric.ball_mem_nhds (0:E) zero_lt_one] with x hx
    have hn:‖x‖ ≤ 1 := (by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < 1).le
    by_cases hx0:x=0
    · simp [hx0,hfd0]
    · exact (hb x hx0 hn).2
  have hdcont:ContinuousAt (fderiv ℝ u) 0 := by
    change Tendsto (fderiv ℝ u) (𝓝 0) (𝓝 (fderiv ℝ u 0))
    rw [hfd0]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hdlim
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨?_,?_⟩,hd0⟩
  · intro x
    by_cases hx:x=0
    · simpa only [hx] using hd0.differentiableAt
    · exact (hu.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)).differentiableAt (by norm_num)
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx:x=0
    · simpa only [hx] using hdcont
    · exact (hu.continuousOn_fderiv_of_isOpen isClosed_singleton.isOpen_compl (by norm_num)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hx)

theorem weighted_H4_global_C1 {u:E→ℝ}
    (hu:ContDiffOn ℝ 2 u ({(0:E)}ᶜ)) (h0:u 0=0)
    {B:ℝ≥0∞} (hB:B≠⊤)
    (hall:∀s:ℝ,-Real.log 2 ≤ s → MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ B) :
    ContDiff ℝ 1 u ∧ HasFDerivAt u (0:E→L[ℝ]ℝ) 0 := by
  obtain ⟨D,hD,hb⟩:=exists_weighted_H4_first_jet_decay_constant
  exact C1_removal_of_sqrt_first_jet_decay hu h0 (mul_nonneg hD ENNReal.toReal_nonneg)
    (hb u hu.continuousOn B hB hall)

#print axioms C1_removal_of_sqrt_first_jet_decay
#print axioms weighted_H4_global_C1
end Yamabe3.Analysis.UniformElliptic
