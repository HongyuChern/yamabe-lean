import Yamabe3.Analysis.NativeSmoothBubblePotential
import Yamabe3.Analysis.NativeCriticalPotentialReaction

/-! The literal omitted smooth bubble potential is an actual critical
Lp class, dominated in norm by the existing uniformly small bubble tail.
The source map retains the factor eight and the same native H1 field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private instance residual32:Fact (1≤(3/2:ℝ≥0∞)):=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

 theorem exists_nativeSmoothBubble_actual_residual_Lp
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (τ:ℝ) {a:ℝ} (ha:0<a) (s:ℝ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hr:∀x:E,0≤χ x ∧ χ x≤1)
    (hχone:∀x∈closedBall (0:E) (Real.exp s),χ x=1)
    (hs:tsupport (fun x:E=>χ (a⁻¹ • x))⊆K):
    ∃q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure,
      (q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e K τ a y-
        nativeScaledSmoothBubblePotential e τ a χ y) ∧
      ‖q‖≤‖nativeBubbleTailLp g e he hei hK hKs τ s (Real.log a)‖:=by
  let B:E→ℝ:=fun x=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)
  have hB:Continuous B:=continuous_const.mul ((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.comp (continuous_const_smul _))
  let d:M→ℝ:=fun y=>nativeScaledFullBubblePotential e K τ a y-nativeScaledSmoothBubblePotential e τ a χ y
  have hd:Measurable d:=(measurable_coordinateExtension_of_measurable e (hB.measurable.indicator hK.measurableSet)).sub
    (measurable_coordinateExtension_of_measurable e (((hχ.continuous.comp (continuous_const_smul _)).measurable).mul hB.measurable))
  have hdom:=nativeSmoothBubble_difference_tail_dominated e K τ ha s χ hr hχone hs
  have hm:MemLp d (3/2:ℝ≥0∞) g.volumeMeasure:=
    (nativeBubbleTail_memLp g e he hei hK hKs τ s (Real.log a)).mono hd.aestronglyMeasurable (Eventually.of_forall hdom)
  let q:=hm.toLp d
  have hq:(q:M→ℝ)=ᵐ[g.volumeMeasure]d:=hm.coeFn_toLp
  refine ⟨q,hq,?_⟩
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hq,nativeBubbleTailLp_ae g e he hei hK hKs τ s (Real.log a)] with y hy hyt
  rw [hy,hyt]
  exact hdom y

#print axioms exists_nativeSmoothBubble_actual_residual_Lp
end Yamabe3.Analysis.SpherePolar
