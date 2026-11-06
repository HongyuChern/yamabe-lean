import Yamabe3.Analysis.NativeSmoothBubbleUniformTruncation

/-! The literal smooth truncation residual vanishes on its actual
inner physical chart ball. Its critical reaction therefore supplies a
genuine source-free receiving region for the same global H1 field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem nativeSmoothBubble_difference_zero_inner
    (e:OpenPartialHomeomorph E M) {K:Set E} (hKs:K⊆e.source) (τ:ℝ) {a:ℝ} (ha:0<a)
    (L:ℝ) (χ:E→ℝ) (hχone:∀x∈closedBall (0:E) L,χ x=1)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆K)
    (hBallK:closedBall (0:E) (a*L)⊆K):
    ∀y∈e '' closedBall (0:E) (a*L),
      nativeScaledFullBubblePotential e K τ a y-nativeScaledSmoothBubblePotential e τ a χ y=0:=by
  rw [nativeSmoothBubble_compact_chart_identity e K τ a χ hs]
  intro y hy
  obtain ⟨x,hx,rfl⟩:=hy
  have hxK:=hBallK hx
  have hxs:=hKs hxK
  have hxU:a⁻¹ • x∈closedBall (0:E) L:=by
    rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
    exact (inv_mul_le_iff₀ ha).mpr (mem_closedBall_zero_iff.mp hx)
  simp only [nativeScaledFullBubblePotential,nativeCompactChartFunction,
    coordinateExtension_comp_apply e _ hxs,indicator_of_mem hxK,hχone _ hxU,one_mul,sub_self]

 theorem nativeSmoothBubble_reaction_zero_on_receiving_ball
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g)
    (e:OpenPartialHomeomorph E M) {K:Set E} (hKs:K⊆e.source) (τ:ℝ) {a:ℝ} (ha:0<a)
    {L:ℝ} (hL:(64:ℝ)≤L) (χ:E→ℝ) (hχone:∀x∈closedBall (0:E) L,χ x=1)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆K)
    (hBallK:closedBall (0:E) (a*L)⊆K)
    (q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure)
    (hq:(q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e K τ a y-nativeScaledSmoothBubblePotential e τ a χ y)):
    ∀z:H1Zero g.leviCivitaData univ,
      (nativeCriticalPotentialReactionCLM g hY q z:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' ball (0:E) (a*64))]0:=by
  have hsrc:ball (0:E) (a*64)⊆e.source:=ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hL ha.le)).trans (hBallK.trans hKs))
  have hΩ:IsOpen (e '' ball (0:E) (a*64)):=e.isOpen_image_of_subset_source isOpen_ball hsrc
  have hz:=nativeSmoothBubble_difference_zero_inner e hKs τ ha L χ hχone hs hBallK
  intro z
  filter_upwards [ae_restrict_of_ae (s:=e '' ball (0:E) (a*64)) (nativeCriticalPotentialReactionCLM_ae g hY q z),
    ae_restrict_of_ae (s:=e '' ball (0:E) (a*64)) hq,ae_restrict_mem hΩ.measurableSet] with y hy hqy hyΩ
  obtain ⟨x,hx,hxy⟩:=hyΩ
  have hyL:y∈e '' closedBall (0:E) (a*L):=⟨x,
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hL ha.le)) (ball_subset_closedBall hx),hxy⟩
  rw [hy,hqy,hz y hyL,zero_mul,mul_zero]
  rfl

#print axioms nativeSmoothBubble_difference_zero_inner
#print axioms nativeSmoothBubble_reaction_zero_on_receiving_ball
end Yamabe3.Analysis.SpherePolar
