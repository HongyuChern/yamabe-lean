import Yamabe3.Analysis.NativeScaledCutoffGeometry
import Yamabe3.Analysis.NativeSmoothBubbleResidualLp

/-! Choose a genuine smooth spatial truncation after a fixed tail
budget and before the independent small physical scale. The omitted
potential is an actual uniformly small critical Lp class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

private instance truncation32:Fact (1≤(3/2:ℝ≥0∞)):=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

 theorem exists_nativeSmoothBubble_uniform_truncation
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0<R₀) (hKs:closedBall (0:E) R₀⊆e.source)
    (τ lower:ℝ) {ε:ℝ} (hε:0<ε):
    ∃s:ℝ,∃χ:E→ℝ,∃hχ:ContDiff ℝ ∞ χ,∃hc:HasCompactSupport χ,∃δ:ℝ,
      max 0 lower ≤ s ∧ 0<δ ∧ (∀x:E,0≤χ x ∧ χ x≤1) ∧
      (∀x∈closedBall (0:E) (Real.exp s),χ x=1) ∧ tsupport χ⊆ball (0:E) (2*Real.exp s) ∧
      ∀a:ℝ,∀ha:0<a,a≤δ→
        tsupport (fun x:E=>χ (a⁻¹ • x))⊆closedBall (0:E) R₀ ∧
        ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χ) ∧
        ∃q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure,
          (q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
            nativeScaledSmoothBubblePotential e τ a χ y) ∧ ‖q‖≤ε:=by
  obtain ⟨s,hs,hsmall⟩:=exists_nativeBubbleTailLp_small_above g e he hei
    (isCompact_closedBall (0:E) R₀) hKs τ lower hε
  obtain ⟨χ,hχ,hc,hr,hχone,hχs⟩:=exists_nativeSmoothBubble_spatial_cutoff (Real.exp_pos s)
  let δ:=R₀/(2*Real.exp s)
  have hδ:0<δ:=by dsimp only [δ];positivity
  refine ⟨s,χ,hχ,hc,δ,hs,hδ,hr,hχone,hχs,fun a ha had=>?_⟩
  have hfit:a*(2*Real.exp s)≤R₀:=(le_div_iff₀ (by positivity:0<2*Real.exp s)).mp had
  have hSupp:tsupport (fun x:E=>χ (a⁻¹ • x))⊆closedBall (0:E) R₀:=by
    intro x hx
    have hχx:a⁻¹ • x∈tsupport χ:=(tsupport_comp_eq_preimage χ
      (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))).le hx
    exact euclideanDilatedBall_subset_closedBall ha hfit (hχs hχx)
  obtain ⟨q,hq,hqn⟩:=exists_nativeSmoothBubble_actual_residual_Lp g e he hei
    (isCompact_closedBall (0:E) R₀) hKs τ ha s χ hχ hr hχone hSupp
  exact ⟨hSupp,nativeScaledSmoothBubblePotential_smooth e hei τ ha χ hχ hc (hSupp.trans hKs),q,hq,
    hqn.trans (hsmall (Real.log a))⟩

#print axioms exists_nativeSmoothBubble_uniform_truncation
end Yamabe3.Analysis.SpherePolar
