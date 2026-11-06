import Yamabe3.Analysis.NativeSmoothBubbleUniformTruncation

/-! Pay a FIXED feedback response cost before choosing the smooth
truncation and the independent physical scale. No smallness of the
whole bubble and no missing contraction estimate is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private instance uniformGap32:Fact (1≤(3/2:ℝ≥0∞)):=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

 theorem exists_nativeSmoothPotential_uniform_strict_gap
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0<R₀) (hKs:closedBall (0:E) R₀⊆e.source)
    (τ lower B:ℝ) (hB:0≤B):
    ∃s:ℝ,∃χ:E→ℝ,∃hχ:ContDiff ℝ ∞ χ,∃hc:HasCompactSupport χ,∃δ:ℝ,
      max 0 lower ≤ s ∧ 64≤Real.exp s ∧ 0<δ ∧ (∀x:E,0≤χ x ∧ χ x≤1) ∧
      (∀x∈closedBall (0:E) (Real.exp s),χ x=1) ∧ tsupport χ⊆ball (0:E) (2*Real.exp s) ∧
      ∀a:ℝ,∀ha:0<a,a≤δ→
        tsupport (fun x:E=>χ (a⁻¹ • x))⊆closedBall (0:E) R₀ ∧
        ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χ) ∧
        ∃q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure,
          (q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
            nativeScaledSmoothBubblePotential e τ a χ y) ∧
          B*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖q‖)≤(1/2:ℝ):=by
  let C:=B*(8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)
  have hC:0≤C:=by dsimp only [C];positivity
  let ε:ℝ:=(1/2)/(C+1)
  have hε:0<ε:=by dsimp only [ε];positivity
  obtain ⟨s,χ,hχ,hc,δ,hs,hδ,hr,hχone,hχs,hStage⟩:=exists_nativeSmoothBubble_uniform_truncation g e he hei hR₀ hKs τ
    (max lower (Real.log 64)) hε
  have hs₀:0 ≤ s:=(le_max_left _ _).trans hs
  have hslow:lower ≤ s:=((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have hs64:Real.log 64 ≤ s:=((le_max_right _ _).trans (le_max_right _ _)).trans hs
  have hL64:(64:ℝ)≤Real.exp s:=by simpa only [Real.exp_log (by norm_num:(0:ℝ)<64)] using Real.exp_le_exp.mpr hs64
  refine ⟨s,χ,hχ,hc,δ,max_le hs₀ hslow,hL64,hδ,hr,hχone,hχs,fun a ha had=>?_⟩
  obtain ⟨hSupp,hSm,q,hq,hqn⟩:=hStage a ha had
  have hbudget:C*ε≤(1/2:ℝ):=by
    dsimp only [ε]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity:0<C+1)).mpr
    nlinarith only [hC]
  refine ⟨hSupp,hSm,q,hq,?_⟩
  calc
    _=C*‖q‖:=by dsimp only [C];ring
    _≤C*ε:=mul_le_mul_of_nonneg_left hqn hC
    _≤1/2:=hbudget

#print axioms exists_nativeSmoothPotential_uniform_strict_gap
end Yamabe3.Analysis.SpherePolar
