import Yamabe3.Analysis.NativeSupportedOuterNewtonValue
import Yamabe3.Analysis.NativeSupportedOuterFarH4

/-! Same complete outer field, same homogeneous model equation,
with the sharper Newton-rate exp(5s/2) weighted H2 and H4 estimates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

 theorem exists_nativeSupportedOuter_Newton_far_H4_bound
    {V W:Set E} (hV:IsOpen V) (hVc:IsCompact (closure V))
    (hVD:closure V⊆nativePoissonEntranceCollar)
    (hW:IsOpen W) (hWc:IsCompact (closure W)) (hWV:closure W⊆V)
    (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃S:ℝ,S≤-(1/2:ℝ) ∧ ∃C:ℝ≥0∞,C≠⊤ ∧
      ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
        (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→∀s:ℝ,s≤S→
      MemWkp 4 2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 W ∧
      iteratedWeakSobolevNorm 4 2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 W≤
        C*ENNReal.ofReal (Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖)) := by
  obtain ⟨Q,hQ,hqj⟩:=exists_fullBubble_far_spatial_potential_jets 2
  obtain ⟨C₄,hC₄,h4⟩:=exists_nativeHomogeneousCollar_H4_bound hV hVc hVD hW hWc hWV hQ
  obtain ⟨C₀,hC₀,h0⟩:=exists_nativeSupportedOuter_Newton_value_decay b ht
  let S:=min (-(1/2:ℝ)) (min (b-1) (-τ-2))
  refine ⟨S,min_le_left _ _,C₄*ENNReal.ofReal C₀,by finiteness,fun F d n σ hσ hF s hs=>?_⟩
  have hs0:s≤-(1/2:ℝ):=hs.trans (min_le_left _ _)
  have hsb:s≤b-1:=hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsc:s≤-τ-2:=hs.trans ((min_le_right _ _).trans (min_le_right _ _))
  let α:=τ+s
  let q:=nativeHalfEndPotentialCoefficient (fullBubblePhasePotential α)
  have hα:α≤0:=by dsimp only [α];linarith only [hsc]
  have hq:ContDiffOn ℝ ∞ q ({0}ᶜ:Set E):=
    nativeHalfEndPotentialCoefficient_contDiffOn (fullBubblePhasePotential α)
      (fullBubbleHighPotential_time_jets α).1
  have hqV:∀n≤2,∀x∈V,‖iteratedFDeriv ℝ n q x‖≤Q:=by
    intro n hn x hx
    have hxD: x∈nativePoissonEntranceCollar:=hVD (subset_closure hx)
    have hxA:=nativeEntranceCollar_closure_subset_basic (subset_closure hxD)
    exact hqj α hα n hn x hxA.1.le hxA.2.le
  have heq:=nativeSupportedOuter_far_weakNegativeLaplacian b ht F d n σ hσ hF hs0 hsb hsc
  rw [←fullBubblePhasePotential_translate τ s] at heq
  have hh:=h4 q hq hqV (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) heq
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hbnd:=ENNReal.ofReal_le_ofReal (h0 F d n σ hσ hF s (by linarith only [hsc]))
  have he:ENNReal.ofReal (C₀*Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖))=
      ENNReal.ofReal C₀*ENNReal.ofReal (Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖)):=by
    rw [mul_assoc,ENNReal.ofReal_mul hC₀]
  rw [he] at hbnd
  exact (mul_le_mul le_rfl hbnd zero_le zero_le).trans_eq (mul_assoc _ _ _).symm

 theorem exists_nativeSupportedOuter_Newton_far_H2_bound
    {V W:Set E} (hV:IsOpen V) (hVc:IsCompact (closure V))
    (hVD:closure V⊆nativePoissonEntranceCollar)
    (hW:IsOpen W) (hWc:IsCompact (closure W)) (hWV:closure W⊆V)
    (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃S:ℝ,S≤-(1/2:ℝ) ∧ ∃C:ℝ≥0∞,C≠⊤ ∧
      ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
        (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→∀s:ℝ,s≤S→
      MemWkp 2 2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 W ∧
      iteratedWeakSobolevNorm 2 2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 W≤
        C*ENNReal.ofReal (Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖)) := by
  obtain ⟨S,hS,C,hC,h⟩:=exists_nativeSupportedOuter_Newton_far_H4_bound hV hVc hVD hW hWc hWV b ht
  refine ⟨S,hS,C,hC,fun F d n σ hσ hF s hs=>?_⟩
  have hh:=h F d n σ hσ hF s hs
  exact ⟨hh.1.le_of_le (by omega),(wkpNorm_mono_order (by omega:2≤4) _ W).trans hh.2⟩

#print axioms exists_nativeSupportedOuter_Newton_far_H4_bound
#print axioms exists_nativeSupportedOuter_Newton_far_H2_bound
end Yamabe3.Analysis.SpherePolar
