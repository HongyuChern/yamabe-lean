import Yamabe3.Analysis.NativeChartLpTransport
import Yamabe3.Analysis.FullBubbleScaledCriticalTail

/-! The actual physical bubble tail transported to the native volume
measure. Compact-chart density costs precede both cutoff and entrance
scales. No smallness of the entire bubble is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private instance nativeTail32 : Fact (1 ≤ (3/2 : ℝ≥0∞)) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

theorem exists_finite_exponential_tail_budget (c : ℝ≥0∞) (hc : c ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃s : ℝ, 0 ≤ s ∧ c*ENNReal.ofReal (Real.exp (-2*s)) ≤ ENNReal.ofReal ε := by
  have he : Tendsto (fun s : ℝ => Real.exp (-2*s)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
    simpa only [Function.comp_def, neg_mul, id_eq] using hh
  have hh : ∀ᶠs : ℝ in atTop, c.toReal*Real.exp (-2*s) < ε := by
    have hl : Tendsto (fun s : ℝ => c.toReal*Real.exp (-2*s)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul he
    exact hl.eventually (gt_mem_nhds hε)
  obtain ⟨s,hs,hsb⟩ := ((eventually_ge_atTop (0 : ℝ)).and hh).exists
  refine ⟨s,hs,?_⟩
  rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hsb.le

theorem nativeBubbleTail_memLp
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ s t : ℝ) :
    MemLp (nativeCompactChartFunction e K (fullBubbleScaledTail τ s t)) (3/2 : ℝ≥0∞) g.volumeMeasure :=
  ((exists_nativeCompactChart_lp_bound g e he hei hK hKs (3/2 : ℝ≥0∞)).choose_spec.2 _
    (memLp_exp_potential_dilation t _ (fullBubblePotentialTail_memLp τ s))).1

def nativeBubbleTailLp
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ s t : ℝ) :
    Lp ℝ (3/2 : ℝ≥0∞) g.volumeMeasure :=
  (nativeBubbleTail_memLp g e he hei hK hKs τ s t).toLp _

theorem nativeBubbleTailLp_ae
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ s t : ℝ) :
    (nativeBubbleTailLp g e he hei hK hKs τ s t : M → ℝ) =ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e K (fullBubbleScaledTail τ s t) :=
  (nativeBubbleTail_memLp g e he hei hK hKs τ s t).coeFn_toLp

theorem exists_nativeBubbleTailLp_small
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃s : ℝ, 0 ≤ s ∧ ∀t : ℝ, ‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ ≤ ε := by
  obtain ⟨D,hD,hd⟩ := exists_nativeCompactChart_lp_bound g e he hei hK hKs (3/2 : ℝ≥0∞)
  let c := D*(ENNReal.ofReal (15*Real.exp (2*τ))*eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume)
  have hc : c ≠ ⊤ := ENNReal.mul_ne_top hD
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top exteriorInverseFourth_memLp_one.eLpNorm_lt_top.ne)
  obtain ⟨s,hs,hb⟩ := exists_finite_exponential_tail_budget c hc hε
  refine ⟨s,hs,fun t => ?_⟩
  have hq := memLp_exp_potential_dilation t _ (fullBubblePotentialTail_memLp τ s)
  have hh := (hd (fullBubbleScaledTail τ s t) hq).2
  have hn : eLpNorm (fullBubbleScaledTail τ s t) (3/2 : ℝ≥0∞) volume =
      eLpNorm (fullBubblePotentialTail τ (Real.exp s)) (3/2 : ℝ≥0∞) volume :=
    eLpNorm_exp_potential_dilation t _
  rw [hn] at hh
  have hj := hh.trans (mul_le_mul le_rfl (fullBubblePotentialTail_critical_norm τ s) zero_le zero_le)
  have hb' : eLpNorm (nativeCompactChartFunction e K (fullBubbleScaledTail τ s t)) (3/2 : ℝ≥0∞) g.volumeMeasure ≤
      ENNReal.ofReal ε := hj.trans ((by simpa only [c,mul_assoc] using hb))
  have hident : ENNReal.ofReal ‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ =
      eLpNorm (nativeCompactChartFunction e K (fullBubbleScaledTail τ s t)) (3/2 : ℝ≥0∞) g.volumeMeasure := by
    rw [ofReal_norm]
    exact Lp.enorm_toLp _
  rw [← hident] at hb'
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hb'

#print axioms exists_finite_exponential_tail_budget
#print axioms nativeBubbleTail_memLp
#print axioms nativeBubbleTailLp_ae
#print axioms exists_nativeBubbleTailLp_small
end Yamabe3.Analysis.SpherePolar
