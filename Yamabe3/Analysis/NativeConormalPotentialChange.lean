import Yamabe3.Analysis.NativeGlobalConormalBalance

/-! A zeroth-order change preserves the physical weak flux ONLY with
the proved SAME-field source adjustment. No potential identity is erased. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeWeakConormal_change_potential
    (g:RiemannianMetric 3 M) (Ω:Set M) (V₀ V₁:M→ℝ)
    (hV₀:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V₀) (hV₁:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V₁)
    (Z:H1Zero g.leviCivitaData univ) (F₀ F₁:Lp ℝ 2 g.volumeMeasure)
    (hF:(F₁:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]
      (fun y=>F₀ y+(V₁ y-V₀ y)*toL2 g.leviCivitaData univ Z y)):
    ∀η:H1Zero g.leviCivitaData univ,
      nativeWeakEnergySourceDataCLM g Ω V₁ hV₁ (Z,F₁) η=
        nativeWeakEnergySourceDataCLM g Ω V₀ hV₀ (Z,F₀) η:=by
  intro η
  rw [nativeWeakEnergySourceDataCLM_apply,nativeWeakEnergySourceDataCLM_apply,
    nativeRestrictedEllipticForm_apply,nativeRestrictedEllipticForm_apply,
    nativeRestrictedPotentialForm_integral,nativeRestrictedPotentialForm_integral,
    nativeRestrictedL2SourceOperator_apply,nativeRestrictedL2SourceOperator_apply]
  dsimp only [Prod.fst,Prod.snd]
  have hi₀:=nativeRestrictedPotentialForm_integrable g Ω V₀ hV₀ Z η
  have hi₁:=nativeRestrictedPotentialForm_integrable g Ω V₁ hV₁ Z η
  have hs₀:=nativeRestrictedL2SourceOperator_integrable g Ω F₀ η
  have hs₁:=nativeRestrictedL2SourceOperator_integrable g Ω F₁ η
  have hh:(∫y in Ω,V₁ y*toL2 g.leviCivitaData univ Z y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)-
      (∫y in Ω,F₁ y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)=
      (∫y in Ω,V₀ y*toL2 g.leviCivitaData univ Z y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)-
      (∫y in Ω,F₀ y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure):=by
    rw [←integral_sub hi₁ hs₁,←integral_sub hi₀ hs₀]
    apply integral_congr_ae
    filter_upwards [hF] with y hy
    rw [hy]
    ring
  linear_combination hh

#print axioms nativeWeakConormal_change_potential
end Yamabe3.Analysis.SpherePolar
