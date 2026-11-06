import Yamabe3.Analysis.NativeOriginalSourceCutoffEnergy
import Yamabe3.Analysis.NativeOuterEnergyCutoff
import Yamabe3.Analysis.NativeCompletedChartScaling

/-! The actual original weighted source has one matched model field
and one native completed field after the SAME far cutoff, dilation and
chart. The bound C*sqrt(a) follows from actual completion maps; no native
PDE or conormal equation is inserted into this energy producer. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def originalNativeNormed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] originalNativeNormed

theorem exists_originalSource_native_cutoff_energy_family
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {κ:ℝ} (hκ0:0 ≤ κ) (hκ1:κ < 1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ)
    {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (S₀:ℝ) (O:Set E) (hO:tsupport (fun y:E=>χ (Real.exp S₀ • y))⊆O) :
    let P:=p.nativeHighPotential hκ0 hκ1
    ∃(T:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
      (L:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc O) (C:ℝ),0 ≤ C ∧
      (∀f:HalfEndPhysicalH2SourceGraph,∃F:E→ℝ,∃hF2:ContDiffOn ℝ 2 F ({0}ᶜ:Set E),
        EqOn (nativeH4GraphFunction (T f)) F (closedBall (0:E) 4) ∧
        (F=ᵐ[volume.restrict (ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f) ∧
        ∃qi wo:ℝ×SpherePolar.S→ℝ,Measurable qi ∧ Measurable wo ∧
          (∀i:HalfEndPhysicalSliceIndex,
            ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T f)).val.1:E→ℝ)
              =ᵐ[volume.restrict nativePoissonEntranceCollar]
                fun x=>Real.exp (3*i.val/2)*(F (Real.exp (-i.val) • x)+cylinderLift qi (Real.exp (-i.val) • x))) ∧
          (∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T f) s) s wo) ∧
          (toL2 Deuc O (L f):E→ℝ)=ᵐ[volume]
            fun y=>χ (Real.exp S₀ • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y) ∧
      ∀a:ℝ,∀ha:0 < a,∀ha1:a ≤ 1,∀hfit:euclideanDilatedDomain a O⊆K,
        ∃Q:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ,‖Q‖ ≤ C*Real.sqrt a ∧
          ∀f:HalfEndPhysicalH2SourceGraph,toL2 g.leviCivitaData univ (Q f)=
            nativeCompactChartL2CLM g e he hei hK hKs (euclideanL2DilationCLM ha ha1 (toL2 Deuc O (L f))) := by
  dsimp only
  obtain ⟨T,L,hL⟩:=exists_originalSource_matched_cutoff_energy hκ0 hκ1 p hp ht χ hχ hc hs h1 S₀ O hO
  let C:=nativeWeakChartBound g e he hei hK hKs*‖L‖
  have hC:0 ≤ C:=mul_nonneg (nativeWeakChartBound_pos g e he hei hK hKs).le (norm_nonneg L)
  refine ⟨T,L,C,hC,hL,fun a ha ha1 hfit=>?_⟩
  let Q:=(nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit).comp L
  refine ⟨Q,?_,fun f=>nativeEuclideanCompletedChartScaleCLM_toL2 g e he hei hK hKs ha ha1 O hfit (L f)⟩
  apply (ContinuousLinearMap.opNorm_comp_le _ L).trans
  exact (mul_le_mul_of_nonneg_right
    (nativeEuclideanCompletedChartScaleCLM_norm g e he hei hK hKs ha ha1 O hfit) (norm_nonneg L)).trans_eq (by dsimp only [C];ring)

#print axioms exists_originalSource_native_cutoff_energy_family
end Yamabe3.Analysis.UniformElliptic
