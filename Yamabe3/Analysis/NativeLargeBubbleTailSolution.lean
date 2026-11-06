import Yamabe3.Analysis.NativeBubbleTailLargeCutoff
import Yamabe3.Analysis.StrictLinearFeedback

/-! A real global native H1 solution with inner tail radius at least 64 after absorbing the actual compact
bubble potential tail. The cutoff, source multiplier and strict gap
are constructed upstream. This is not the full exterior gluing inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def largeTailSolutionH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] largeTailSolutionH1Normed
private instance largeTailSolution65 : Fact (1 ≤ (6/5 : ℝ≥0∞)) := ⟨one_le_sixFifths⟩

def nativeLargeBubbleTailCutoff
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ) : ℝ :=
  (exists_nativeBubbleTail_strict_gap_above g hY e he hei hK hKs τ (Real.log 64)).choose

def nativeLargeBubbleTailSolutionCLM
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ)
    (b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall : 60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g) (t : ℝ) :
    Lp ℝ (6/5 : ℝ≥0∞) g.volumeMeasure →L[ℝ] H1Zero g.leviCivitaData univ :=
  strictFeedbackCLM (closedSixFifthsJacobianSolutionCLM g hY b hb hsmall)
    (nativeBubbleTailSourceCLM g hY e he hei hK hKs τ (nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ) t)
    (q := (1/2 : ℝ≥0)) (by norm_num)
    ((exists_nativeBubbleTail_strict_gap_above g hY e he hei hK hKs τ (Real.log 64)).choose_spec.2 b hb hsmall t)

theorem nativeLargeBubbleTailSolutionCLM_fixed
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ)
    (b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall : 60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g) (t : ℝ)
    (F : Lp ℝ (6/5 : ℝ≥0∞) g.volumeMeasure) :
    let s := nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ
    let u := nativeLargeBubbleTailSolutionCLM g hY e he hei hK hKs τ b hb hsmall t F
    closedSixFifthsJacobianSolutionCLM g hY b hb hsmall
      (F+nativeBubbleTailSourceCLM g hY e he hei hK hKs τ s t u)=u :=
  strictFeedback_fixed _ _ (q := (1/2 : ℝ≥0)) (by norm_num)
    ((exists_nativeBubbleTail_strict_gap_above g hY e he hei hK hKs τ (Real.log 64)).choose_spec.2 b hb hsmall t) F

theorem nativeLargeBubbleTailSolutionCLM_norm
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ)
    (b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall : 60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g) (t : ℝ) :
    ‖nativeLargeBubbleTailSolutionCLM g hY e he hei hK hKs τ b hb hsmall t‖ ≤
      2*‖closedSixFifthsJacobianSolutionCLM g hY b hb hsmall‖ := by
  have hh := strictFeedbackCLM_norm (closedSixFifthsJacobianSolutionCLM g hY b hb hsmall)
    (nativeBubbleTailSourceCLM g hY e he hei hK hKs τ (nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ) t)
    (q := (1/2 : ℝ≥0)) (by norm_num)
    ((exists_nativeBubbleTail_strict_gap_above g hY e he hei hK hKs τ (Real.log 64)).choose_spec.2 b hb hsmall t)
  exact hh.trans_eq (by norm_num; ring)

theorem nativeLargeBubbleTailSolutionCLM_weak
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ)
    (b : M → ℝ) (hb : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall : 60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3 : ℝ) ≤ Target.yamabeConstant g) (t : ℝ)
    (F : Lp ℝ (6/5 : ℝ≥0∞) g.volumeMeasure) :
    let s := nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ
    let u := nativeLargeBubbleTailSolutionCLM g hY e he hei hK hKs τ b hb hsmall t F
    ∀η : H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g b hb u η =
        ∫x,(F x+8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ s t) x*
          toL2 g.leviCivitaData univ u x))*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure := by
  dsimp only
  let s := nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ
  let u := nativeLargeBubbleTailSolutionCLM g hY e he hei hK hKs τ b hb hsmall t F
  let A := nativeBubbleTailSourceCLM g hY e he hei hK hKs τ s t
  let G := F+A u
  have heq : closedSixFifthsJacobianSolutionCLM g hY b hb hsmall G=u :=
    nativeLargeBubbleTailSolutionCLM_fixed g hY e he hei hK hKs τ b hb hsmall t F
  intro η
  calc
    _ = closedYamabeJacobianForm g b hb (closedSixFifthsJacobianSolutionCLM g hY b hb hsmall G) η := by rw [heq]
    _ = ∫x,G x*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure := by
      change closedYamabeJacobianForm g b hb
        (closedYamabeJacobianInverse g hY b hb hsmall (closedSixFifthsForcing g hY G)) η = _
      rw [closedYamabeJacobianInverse_spec,closedSixFifthsForcing_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add F (A u),nativeBubbleTailSourceCLM_ae g hY e he hei hK hKs τ s t u] with x hx hAx
      change (F+A u) x*_ = _
      rw [hx]
      change (F x+(A u : M → ℝ) x)*_ = _
      have hAu : (A u : M → ℝ) x = 8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ s t) x*
          toL2 g.leviCivitaData univ u x) := by convert! hAx using 1
      rw [hAu]

theorem nativeLargeBubbleTailCutoff_radius_ge
    (g : RiemannianMetric 3 M) (hY : 0 < Target.yamabeConstant g) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (τ : ℝ) :
    64 ≤ Real.exp (nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ) := by
  have hh : Real.log 64 ≤ nativeLargeBubbleTailCutoff g hY e he hei hK hKs τ :=
    (le_max_right 0 (Real.log 64)).trans
      (exists_nativeBubbleTail_strict_gap_above g hY e he hei hK hKs τ (Real.log 64)).choose_spec.1
  calc
    (64 : ℝ) = Real.exp (Real.log 64) := (Real.exp_log (by norm_num : (0 : ℝ) < 64)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hh

#print axioms nativeLargeBubbleTailCutoff_radius_ge
#print axioms nativeLargeBubbleTailSolutionCLM_fixed
#print axioms nativeLargeBubbleTailSolutionCLM_norm
#print axioms nativeLargeBubbleTailSolutionCLM_weak
end Yamabe3.Analysis.SpherePolar
