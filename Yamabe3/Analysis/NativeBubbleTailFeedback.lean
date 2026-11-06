import Yamabe3.Analysis.NativeBubbleTailLp
import Yamabe3.Analysis.NativeSixFifthsForcing
import Mathlib.MeasureTheory.Function.Holder

/-! Actual compact-chart bubble-tail feedback into the closed native
energy space. The strict gap is derived from the potential tail and the
proved uniform background inverse, not supplied as an input. This does
not include the other exterior/source/boundary feedback components. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def tailFeedbackH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] tailFeedbackH1Normed
private instance tailFeedback32 : Fact (1 ≤ (3/2 : ℝ≥0∞)) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩
private instance tailFeedback6 : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
private instance tailFeedback65 : Fact (1 ≤ (6/5 : ℝ≥0∞)) := ⟨one_le_sixFifths⟩
private instance tailFeedbackHolder : ENNReal.HolderTriple (3/2) 6 (6/5) := by
  constructor
  have h32 : (3/2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  have h65 : (6/5 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr h32, by norm_num⟩)
    (ENNReal.inv_ne_top.mpr h65)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

def nativeBubbleTailSourceCLM
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ s t : ℝ) :
    H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ (6/5 : ℝ≥0∞) g.volumeMeasure :=
  (8 : ℝ) • (((ContinuousLinearMap.mul ℝ ℝ).holderL g.volumeMeasure (3/2) 6 (6/5)
    (nativeBubbleTailLp g e he hei hK hKs τ s t)).comp (GreenMass.NativeEnergyL6.toL6 g hY))

theorem nativeBubbleTailSourceCLM_ae
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ s t : ℝ)
    (w : H1Zero g.leviCivitaData univ) :
    (nativeBubbleTailSourceCLM g hY e he hei hK hKs τ s t w : M → ℝ) =ᵐ[g.volumeMeasure]
      (fun x => 8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ s t) x*
        toL2 g.leviCivitaData univ w x)) := by
  let Q := nativeBubbleTailLp g e he hei hK hKs τ s t
  let v := GreenMass.NativeEnergyL6.toL6 g hY w
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := (6/5 : ℝ≥0∞)) Q v
  have hs := Lp.coeFn_smul (8 : ℝ) ((ContinuousLinearMap.mul ℝ ℝ).holder (6/5 : ℝ≥0∞) Q v)
  filter_upwards [hh,hs,nativeBubbleTailLp_ae g e he hei hK hKs τ s t,
    GreenMass.NativeEnergyL6.toL6_ae_toL2 g hY w] with x hx hsx hqx hvx
  change ((8 : ℝ) • ((ContinuousLinearMap.mul ℝ ℝ).holder (6/5 : ℝ≥0∞) Q v) : Lp ℝ (6/5 : ℝ≥0∞) g.volumeMeasure) x = _
  calc
    _ = 8*((ContinuousLinearMap.mul ℝ ℝ).holder (6/5 : ℝ≥0∞) Q v : M → ℝ) x := by
      convert! hsx using 1 <;> rfl
    _ = _ := by rw [hx,ContinuousLinearMap.mul_apply',hqx,hvx]

theorem nativeBubbleTailSourceCLM_norm
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ s t : ℝ) :
    ‖nativeBubbleTailSourceCLM g hY e he hei hK hKs τ s t‖ ≤
      (8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ := by
  let B := (ContinuousLinearMap.mul ℝ ℝ).holderL g.volumeMeasure (3/2) 6 (6/5)
  let Q := nativeBubbleTailLp g e he hei hK hKs τ s t
  have hB : ‖B‖ ≤ 1 := (ContinuousLinearMap.mul ℝ ℝ).norm_holderL_le.trans (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
  have hBQ : ‖B Q‖ ≤ ‖Q‖ := (B.le_opNorm Q).trans
    ((mul_le_mul_of_nonneg_right hB (norm_nonneg Q)).trans_eq (one_mul _))
  change ‖(8 : ℝ) • ((B Q).comp (GreenMass.NativeEnergyL6.toL6 g hY))‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  exact (mul_le_mul_of_nonneg_left
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hBQ (norm_nonneg _))) (by norm_num)).trans_eq (by ring)

theorem exists_nativeBubbleTail_strict_gap
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ) :
    ∃s : ℝ, 0 ≤ s ∧ ∀(b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
      (hsmall : 60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g) (t : ℝ),
      ‖closedSixFifthsJacobianSolutionCLM g hY b hb hsmall‖*
        ‖nativeBubbleTailSourceCLM g hY e he hei hK hKs τ s t‖ ≤ (1/2 : ℝ) := by
  obtain ⟨C,hC,hcb⟩ := exists_uniform_closedSixFifthsJacobianSolution_bound g hY
  let N := C*(8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)
  have hN : 0 ≤ N := by positivity
  let δ := (1/2 : ℝ)/(N+1)
  have hδ : 0 < δ := by positivity
  obtain ⟨s,hs,hq⟩ := exists_nativeBubbleTailLp_small g e he hei hK hKs τ hδ
  refine ⟨s,hs,fun b hb hsmall t => ?_⟩
  calc
    _ ≤ C*((8*‖GreenMass.NativeEnergyL6.toL6 g hY‖)*‖nativeBubbleTailLp g e he hei hK hKs τ s t‖) :=
      mul_le_mul (hcb b hb hsmall).1 (nativeBubbleTailSourceCLM_norm g hY e he hei hK hKs τ s t) (norm_nonneg _) hC.le
    _ = N*‖nativeBubbleTailLp g e he hei hK hKs τ s t‖ := by dsimp only [N]; ring
    _ ≤ N*δ := mul_le_mul_of_nonneg_left (hq t) hN
    _ ≤ 1/2 := by
      dsimp only [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < N+1)).mpr
      nlinarith

#print axioms nativeBubbleTailSourceCLM_ae
#print axioms nativeBubbleTailSourceCLM_norm
#print axioms exists_nativeBubbleTail_strict_gap
end Yamabe3.Analysis.SpherePolar
