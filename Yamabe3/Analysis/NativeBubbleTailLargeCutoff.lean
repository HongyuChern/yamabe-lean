import Yamabe3.Analysis.NativeBubbleTailFeedback

/-! Choose the actual tail cutoff beyond any prescribed fixed radius,
while retaining the derived uniform strict gap. This supplies room
around the actual entrance sphere before applying homogeneous H4 bounds. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
open UniformElliptic
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def largeTailH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (PoincareMT.LeviCivitaData.Dirichlet.H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] largeTailH1Normed
private instance largeTail32 : Fact (1 ≤ (3/2 : ℝ≥0∞)) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

theorem fullBubbleScaledTail_norm_mono (τ t : ℝ) {s s' : ℝ} (hss : s ≤ s') (x : E) :
    ‖fullBubbleScaledTail τ s' t x‖ ≤ ‖fullBubbleScaledTail τ s t x‖ := by
  dsimp only [fullBubbleScaledTail,fullBubblePotentialTail]
  by_cases hx : Real.exp s' < ‖Real.exp (-t) • x‖
  · have hy := (Real.exp_le_exp.mpr hss).trans_lt hx
    simp only [indicator,mem_setOf_eq,if_pos hx,if_pos hy]
    exact le_refl _
  · simp only [indicator,mem_setOf_eq,if_neg hx,mul_zero,norm_zero]
    exact norm_nonneg _

theorem nativeBubbleTailLp_norm_mono
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ t : ℝ)
    {s s' : ℝ} (hss : s ≤ s') :
    ‖nativeBubbleTailLp g e he hei hK hKs τ s' t‖ ≤ ‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ := by
  have hb : ∀y : M, ‖nativeCompactChartFunction e K (fullBubbleScaledTail τ s' t) y‖ ≤
      ‖nativeCompactChartFunction e K (fullBubbleScaledTail τ s t) y‖ := by
    intro y
    by_cases hy : y∈e.target
    · simp only [nativeCompactChartFunction,coordinateExtension_apply e _ hy]
      by_cases hk : e.symm y∈K
      · simp only [indicator_of_mem hk]
        exact fullBubbleScaledTail_norm_mono τ t hss _
      · simp only [indicator_of_notMem hk,norm_zero,le_refl]
    · simp only [nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy,norm_zero,le_refl]
  have hi := eLpNorm_mono_ae (μ := g.volumeMeasure) (p := (3/2 : ℝ≥0∞)) (Filter.Eventually.of_forall hb)
  have hn (r : ℝ) : ENNReal.ofReal ‖nativeBubbleTailLp g e he hei hK hKs τ r t‖ =
      eLpNorm (nativeCompactChartFunction e K (fullBubbleScaledTail τ r t)) (3/2 : ℝ≥0∞) g.volumeMeasure := by
    rw [ofReal_norm]
    exact Lp.enorm_toLp _
  rw [← hn s',← hn s] at hi
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp hi

theorem exists_nativeBubbleTailLp_small_above
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃s : ℝ, max 0 L ≤ s ∧ ∀t : ℝ, ‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ ≤ ε := by
  obtain ⟨s,hs,hb⟩ := exists_nativeBubbleTailLp_small g e he hei hK hKs τ hε
  refine ⟨max s (max 0 L),le_max_right _ _,fun t => ?_⟩
  exact (nativeBubbleTailLp_norm_mono g e he hei hK hKs τ t (le_max_left _ _)).trans (hb t)

theorem exists_nativeBubbleTail_strict_gap_above
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ L : ℝ) :
    ∃s : ℝ, max 0 L ≤ s ∧ ∀(b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
      (hsmall : 60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g) (t : ℝ),
      ‖closedSixFifthsJacobianSolutionCLM g hY b hb hsmall‖*
        ‖nativeBubbleTailSourceCLM g hY e he hei hK hKs τ s t‖ ≤ (1/2 : ℝ) := by
  obtain ⟨C,hC,hcb⟩ := exists_uniform_closedSixFifthsJacobianSolution_bound g hY
  let N := C*(8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)
  have hN : 0 ≤ N := by positivity
  let δ := (1/2 : ℝ)/(N+1)
  have hδ : 0 < δ := by positivity
  obtain ⟨s,hs,hq⟩ := exists_nativeBubbleTailLp_small_above g e he hei hK hKs τ L hδ
  refine ⟨s,hs,fun b hb hsmall t => ?_⟩
  calc
    _ ≤ C*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖nativeBubbleTailLp g e he hei hK hKs τ s t‖) :=
      mul_le_mul (hcb b hb hsmall).1 (nativeBubbleTailSourceCLM_norm g hY e he hei hK hKs τ s t) (norm_nonneg _) hC.le
    _ = N*‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ := by dsimp only [N];ring
    _ ≤ N*δ := mul_le_mul_of_nonneg_left (hq t) hN
    _ ≤ 1/2 := by
      dsimp only [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < N+1)).mpr
      nlinarith

#print axioms fullBubbleScaledTail_norm_mono
#print axioms nativeBubbleTailLp_norm_mono
#print axioms exists_nativeBubbleTailLp_small_above
#print axioms exists_nativeBubbleTail_strict_gap_above
end Yamabe3.Analysis.SpherePolar
