import Yamabe3.Analysis.NativeOuterEnergyCutoff
import Yamabe3.Analysis.NativeCompletedChartScaling

/-! The actual coupled-model source family has a bounded native H1
field after the fixed far cutoff, physical dilation and actual chart.
The same Euclidean L2 class is used throughout. This is the field
producer; the native PDE and conormal cancellation are separate gates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def twoSidedNativeEnergyNormed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] twoSidedNativeEnergyNormed

theorem exists_nativeTwoSided_native_cutoff_energy_family
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (S₀:ℝ) (O:Set E) (hO:tsupport (fun y:E=>χ (Real.exp S₀ • y))⊆O) :
    ∃(L:NativeTwoSidedSource →L[ℝ] H1Zero Deuc O) (C:ℝ),0 ≤ C ∧
      (∀X:NativeTwoSidedSource,∃wi wo:ℝ×S→ℝ,Measurable wi ∧ Measurable wo ∧
        (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s X) s wi) ∧
        (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s) s wo) ∧
        (toL2 Deuc O (L X):E→ℝ)=ᵐ[volume]
          fun y=>χ (Real.exp S₀ • y)*(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wo) y) ∧
      ∀a:ℝ,∀ha:0 < a,∀ha1:a ≤ 1,∀hfit:euclideanDilatedDomain a O⊆K,
        ∃T:NativeTwoSidedSource →L[ℝ] H1Zero g.leviCivitaData univ,‖T‖ ≤ C*Real.sqrt a ∧
          ∀X:NativeTwoSidedSource,toL2 g.leviCivitaData univ (T X)=
            nativeCompactChartL2CLM g e he hei hK hKs (euclideanL2DilationCLM ha ha1 (toL2 Deuc O (L X))) := by
  obtain ⟨L,hL⟩:=exists_nativeTwoSided_cutoff_energy_family P hp v hv hb b ht χ hχ hc hs h1 S₀ O hO
  let C:=nativeWeakChartBound g e he hei hK hKs*‖L‖
  have hC:0 ≤ C:=mul_nonneg (nativeWeakChartBound_pos g e he hei hK hKs).le (norm_nonneg L)
  refine ⟨L,C,hC,hL,fun a ha ha1 hfit=>?_⟩
  let T:=(nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit).comp L
  refine ⟨T,?_,fun X=>nativeEuclideanCompletedChartScaleCLM_toL2 g e he hei hK hKs ha ha1 O hfit (L X)⟩
  apply (ContinuousLinearMap.opNorm_comp_le _ L).trans
  exact (mul_le_mul_of_nonneg_right
    (nativeEuclideanCompletedChartScaleCLM_norm g e he hei hK hKs ha ha1 O hfit) (norm_nonneg L)).trans_eq (by dsimp only [C];ring)

#print axioms exists_nativeTwoSided_native_cutoff_energy_family
end Yamabe3.Analysis.SpherePolar
