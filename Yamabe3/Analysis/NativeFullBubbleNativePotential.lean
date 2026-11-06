import Yamabe3.Analysis.NativeBubbleTailBoundedL2
import Yamabe3.Analysis.PhysicalBubbleTailSupport

/-! Fixed-scale full native compact-chart bubble potential and the EXACT
same tail. Their difference and the core-tail exclusion are pointwise
identities. A hard chart truncation is not identified with a smooth
paper cutoff by these definitions or bounds. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M]

 def nativeScaledFullBubblePotential (e:OpenPartialHomeomorph E M) (K:Set E) (τ a:ℝ):M→ℝ:=
  nativeCompactChartFunction e K (fun x:E=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))

 theorem fullBubbleScaledTail_actual_scale {a:ℝ} (ha:0<a) (τ c:ℝ):
    fullBubbleScaledTail τ c (Real.log a)=
      (fun x:E=>(a⁻¹)^2*fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x)):=by
  funext x
  simp only [fullBubbleScaledTail,Real.exp_neg,Real.exp_log ha]
  rw [show -2*Real.log a=(-Real.log a)+(-Real.log a) by ring,Real.exp_add,Real.exp_neg,Real.exp_log ha,pow_two]

 theorem nativeBubbleTail_minus_full
    (e:OpenPartialHomeomorph E M) (K:Set E) {a:ℝ} (ha:0<a) (τ c:ℝ):
    (fun y=>nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y-
      nativeScaledFullBubblePotential e K τ a y)=
    nativeCompactChartFunction e K
      (fun x:E=>(a⁻¹)^2*(fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x)-
        fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))):=by
  rw [fullBubbleScaledTail_actual_scale ha]
  have hh:=(nativeCompactChartFunctionLinear e K).map_sub
    (fun x:E=>(a⁻¹)^2*fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x))
    (fun x:E=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))
  change (nativeCompactChartFunctionLinear e K) (fun x:E=>(a⁻¹)^2*fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x))-
    (nativeCompactChartFunctionLinear e K) (fun x:E=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x))=_
  rw [←hh]
  change nativeCompactChartFunction e K
    ((fun x:E=>(a⁻¹)^2*fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x))-
      (fun x:E=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)))=
    nativeCompactChartFunction e K (fun x:E=>(a⁻¹)^2*(fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x)-
      fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)))
  apply congrArg (nativeCompactChartFunction e K)
  funext x
  change (a⁻¹)^2*fullBubblePotentialTail τ (Real.exp c) (a⁻¹ • x)-(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)=_
  ring

 theorem nativeBubbleTail_core_product_zero
    (e:OpenPartialHomeomorph E M) (K:Set E) {a:ℝ} (ha:0<a) (τ:ℝ) {c:ℝ} (hc:Real.log 128≤c)
    (χ:E→ℝ) (hs:tsupport χ⊆ball (0:E) 3):
    ∀y:M,nativeCompactChartFunction e K (fullBubbleScaledTail τ c (Real.log a)) y*
      coordinateExtension e (fun x:E=>χ (a⁻¹ • x)) y=0:=by
  intro y
  by_cases hy:y∈e.target
  · rw [nativeCompactChartFunction,coordinateExtension_apply e _ hy,coordinateExtension_apply e _ hy]
    by_cases hxK:e.symm y∈K
    · rw [indicator_of_mem hxK]
      by_cases hz:χ (a⁻¹ • e.symm y)=0
      · rw [hz,mul_zero]
      · have hball:a⁻¹ • e.symm y∈ball (0:E) 3:=hs (subset_tsupport _ (Function.mem_support.mpr hz))
        have hnorm:‖e.symm y‖≤a*Real.exp c:=by
          have hh:=mem_ball_zero_iff.mp hball
          rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le] at hh
          have h3:‖e.symm y‖<a*3:=(inv_mul_lt_iff₀ ha).mp hh
          have hec:(128:ℝ)≤Real.exp c:=by
            simpa only [Real.exp_log (by norm_num:(0:ℝ)<128)] using Real.exp_le_exp.mpr hc
          exact h3.le.trans (mul_le_mul_of_nonneg_left (by linarith:(3:ℝ)≤Real.exp c) ha.le)
        rw [fullBubbleScaledTail_zero_inner τ c a ha _ hnorm,zero_mul]
    · rw [indicator_of_notMem hxK,zero_mul]
  · simp only [nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy,zero_mul]

section Bounded
variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
 theorem exists_nativeFullBubble_bounded_L2_multiplier
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M) {K:Set E} (hK:IsCompact K) (τ a:ℝ):
    ∃C:ℝ,0≤C ∧ ∃T:Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 g.volumeMeasure,
      ‖T‖≤C ∧ ∀F:Lp ℝ 2 g.volumeMeasure,
        (T F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e K τ a y*F y):=by
  let f:E→ℝ:=fun x=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)
  have hf:Continuous f:=continuous_const.mul
    ((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.comp (continuous_const_smul _))
  obtain ⟨D,hD⟩:=hK.exists_bound_of_continuousOn hf.continuousOn
  let C:=max D 0
  have hC:0≤C:=le_max_right _ _
  let q:=nativeScaledFullBubblePotential e K τ a
  have hq:Measurable q:=measurable_coordinateExtension_of_measurable e (hf.measurable.indicator hK.measurableSet)
  have hqb(y:M):‖q y‖≤C:=by
    by_cases hy:y∈e.target
    · change ‖nativeCompactChartFunction e K f y‖≤C
      rw [nativeCompactChartFunction,coordinateExtension_apply e _ hy]
      by_cases hx:e.symm y∈K
      · rw [indicator_of_mem hx]
        exact (hD _ hx).trans (le_max_left _ _)
      · rw [indicator_of_notMem hx,norm_zero]
        exact hC
    · simp only [q,nativeScaledFullBubblePotential,nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy,norm_zero]
      exact hC
  let T:Lp ℝ 2 g.volumeMeasure →L[ℝ] Lp ℝ 2 g.volumeMeasure:=
    l2ScalarMulCLM q hq.aestronglyMeasurable C hC (Eventually.of_forall hqb)
  refine ⟨C,hC,T,?_,l2ScalarMul_ae q hq.aestronglyMeasurable C hC (Eventually.of_forall hqb)⟩
  exact T.opNorm_le_bound hC (fun F=>l2ScalarMul_norm_le q hq.aestronglyMeasurable C hC (Eventually.of_forall hqb) F)
end Bounded

#print axioms fullBubbleScaledTail_actual_scale
#print axioms nativeBubbleTail_minus_full
#print axioms nativeBubbleTail_core_product_zero
#print axioms exists_nativeFullBubble_bounded_L2_multiplier
end Yamabe3.Analysis.SpherePolar
