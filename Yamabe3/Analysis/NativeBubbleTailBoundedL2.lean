import Yamabe3.Analysis.NativeBubbleTailLargeCutoff
import Yamabe3.Analysis.FullBubbleRegularSource
import Yamabe3.Analysis.L2BoundedScalarMultiplier

/-! At each FIXED physical scale, the actual compact native tail is a
bounded measurable multiplier on L2. This is a fixed-scale bound, not a
uniform small L2 estimate or identification with a smooth target potential. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem exists_nativeBubbleTail_bounded_L2_multiplier
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    {K:Set E} (hK:IsCompact K) (τ c t:ℝ):
    ∃C:ℝ,0≤C ∧∃T:Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 g.volumeMeasure,
      ‖T‖≤C ∧∀F:Lp ℝ 2 g.volumeMeasure,
        (T F:M→ℝ)=ᵐ[g.volumeMeasure]fun y=>
          nativeCompactChartFunction e K (fullBubbleScaledTail τ c t) y*F y:=by
  let B:E→ℝ:=fun x=>Real.exp (-2*t)*fullBubbleSpatialPotential (Real.exp τ) (Real.exp (-t) • x)
  have hB:Continuous B:=continuous_const.mul
    ((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.comp (continuous_const_smul _))
  obtain ⟨D,hD⟩:=hK.exists_bound_of_continuousOn hB.continuousOn
  let C:=max D 0
  have hC:0≤C:=le_max_right _ _
  have hb(x:E)(hx:x∈K):‖fullBubbleScaledTail τ c t x‖≤C:=by
    by_cases hz:Real.exp c<‖Real.exp (-t) • x‖
    · have he:fullBubbleScaledTail τ c t x=B x:=by
        simp only [fullBubbleScaledTail,fullBubblePotentialTail,indicator_of_mem (show Real.exp (-t) • x∈{y:E|Real.exp c<‖y‖} from hz),B]
      rw [he]
      exact (hD x hx).trans (le_max_left _ _)
    · simp only [fullBubbleScaledTail,fullBubblePotentialTail,indicator_of_notMem (show Real.exp (-t) • x∉{y:E|Real.exp c<‖y‖} from hz),mul_zero,norm_zero]
      exact hC
  let q:M→ℝ:=nativeCompactChartFunction e K (fullBubbleScaledTail τ c t)
  have hq:Measurable q:=by
    have ht:Measurable (fullBubbleScaledTail τ c t):=by
      have hu0:Measurable (fullBubblePotentialTail τ (Real.exp c)):=
        (fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.measurable.indicator
          (measurableSet_lt (measurable_const (a:=Real.exp c)) measurable_norm)
      have hu:Measurable (fun x:E=>fullBubblePotentialTail τ (Real.exp c) (Real.exp (-t) • x)):=
        hu0.comp (continuous_const_smul (Real.exp (-t))).measurable
      exact hu.const_mul _
    exact measurable_coordinateExtension_of_measurable e (ht.indicator hK.measurableSet)
  have hqb(y:M):‖q y‖≤C:=by
    by_cases hy:y∈e.target
    · dsimp only [q,nativeCompactChartFunction]
      rw [coordinateExtension_apply e _ hy]
      by_cases hx:e.symm y∈K
      · rw [indicator_of_mem hx]
        exact hb _ hx
      · rw [indicator_of_notMem hx,norm_zero]
        exact hC
    · simp only [q,nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy,norm_zero]
      exact hC
  let T:Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 g.volumeMeasure:=
    l2ScalarMulCLM q hq.aestronglyMeasurable C hC (Eventually.of_forall hqb)
  have hT(F:Lp ℝ 2 g.volumeMeasure):(T F:M→ℝ)=ᵐ[g.volumeMeasure]fun y=>q y*F y:=
    l2ScalarMul_ae q hq.aestronglyMeasurable C hC (Eventually.of_forall hqb) F
  refine ⟨C,hC,T,?_,hT⟩
  apply T.opNorm_le_bound hC
  intro F
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hT F] with y hy
  rw [hy,norm_mul]
  exact mul_le_mul_of_nonneg_right (hqb y) (norm_nonneg _)

#print axioms exists_nativeBubbleTail_bounded_L2_multiplier
end Yamabe3.Analysis.SpherePolar
