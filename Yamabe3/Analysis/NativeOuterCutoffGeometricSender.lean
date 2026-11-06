import Yamabe3.Analysis.NativeOuterGeometricPhysicalSender
import Yamabe3.Analysis.NativeCollarJetMultiplier

/-! Full geometry of the actual OUTER CUTOFF PRODUCT. The cutoff acts
on the true closed jet before the native error operator, so its mixed
principal terms are included. The fixed cutoff cost is explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private instance outerCutoff65:Fact (1 ≤ (6/5:ℝ≥0∞)) := ⟨one_le_sixFifths⟩

def nativeOuterFieldCutoffAtScale (S s:ℝ) (χ:E→ℝ) : E→ℝ :=
  fun y=>χ (Real.exp (S-s) • y)

theorem nativeOuterFieldCutoffAtScale_smooth (S s:ℝ) {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (nativeOuterFieldCutoffAtScale S s χ) :=
  hχ.comp (contDiff_id.const_smul _)

theorem exists_nativeOuter_cutoff_geometric_sender
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ) :
    ∃C:ℝ,0 ≤ C ∧ ∀a:ℝ,0 < a → ∀s:ℝ,s ≤ 0 → a*Real.exp (-s) ≤ 1 →
      ∀S:ℝ,∀(χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ),
      let Mχ:=nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χ)
        (nativeOuterFieldCutoffAtScale_smooth S s hχ)
      ∃T:NativeTwoSidedSource →L[ℝ] Lp ℝ (6/5:ℝ≥0∞) g.volumeMeasure,
        ‖T‖ ≤ C*‖Mχ‖*a*Real.sqrt a*Real.exp (-3*s) ∧ ∀X:NativeTwoSidedSource,
          let U:=nativeBCFCollarErrorCLM gE (a*Real.exp (-s))
            (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
            (Mχ (nativeSupportedOuterAllScaleJet b ht X.2
              (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
              (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X)
              (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X) s)).val
          MemLp (nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U)) 2 g.volumeMeasure ∧
          (T X:M→ℝ)=ᵐ[g.volumeMeasure]nativeDensityCorrectedChartSource gE e K (nativePhysicalShellSource a s U) := by
  obtain ⟨DS,hDS,hsender⟩:=exists_nativePhysicalShellSource_critical_CLM g gE e he hei hK hKs
  obtain ⟨CM,hCM,hmodel⟩:=exists_nativeSupportedTwoSided_all_scale_CLM P hp v hv hb b ht
  obtain ⟨CG,hCG,hgeo⟩:=exists_native_bcf_full_collar_error_linear_bound
    ({()}:Finset Unit) (fun _=>gE) (fun _ _=>hB) (fun _ _=>hρ)
    (norm_nonneg (fullBubblePhasePotential τ))
  refine ⟨DS*CG*CM,by positivity,fun a ha s hs hr S χ hχ=>?_⟩
  dsimp only
  let Mχ:=nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χ)
    (nativeOuterFieldCutoffAtScale_smooth S s hχ)
  obtain ⟨J,hJ,hJv⟩:=hmodel s hs
  obtain ⟨N,hN,hNv⟩:=hsender a ha s
  let G:=nativeBCFCollarErrorCLM gE (a*Real.exp (-s))
    (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
  let U:=G.comp (nativeCollarJetClosure.subtypeL.comp (Mχ.comp J))
  let T:=N.comp U
  have hU (X:NativeTwoSidedSource):‖U X‖ ≤ (CG*a*Real.exp (-s)*‖Mχ‖*CM)*‖X‖ := by
    have hh:=hgeo (a*Real.exp (-s)) (by positivity) hr () (by simp)
      (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (boundedTimeTranslate_norm ℝ s (fullBubblePhasePotential τ)).le (Mχ (J X)).val
    have hm:‖Mχ (J X)‖ ≤ ‖Mχ‖*(CM*‖X‖) :=
      (Mχ.le_opNorm (J X)).trans (mul_le_mul_of_nonneg_left (J.le_of_opNorm_le hJ X) (norm_nonneg Mχ))
    exact (hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))).trans_eq (by ring)
  have hT (X:NativeTwoSidedSource):‖T X‖ ≤
      (DS*CG*CM*‖Mχ‖*a*Real.sqrt a*Real.exp (-3*s))*‖X‖ := by
    have hn:‖N (U X)‖ ≤ (DS*Real.sqrt a*Real.exp (-2*s))*‖U X‖ := N.le_of_opNorm_le hN (U X)
    apply (hn.trans (mul_le_mul_of_nonneg_left (hU X) (by positivity))).trans_eq
    rw [show -3*s=(-2*s)+(-s) by ring,Real.exp_add]
    ring
  refine ⟨T,T.opNorm_le_bound (by positivity) hT,?_⟩
  intro X
  have hh:=hNv (U X)
  dsimp only [U,ContinuousLinearMap.comp_apply] at hh
  rw [hJv X] at hh
  simpa [G,T,U,Mχ,hJv X] using hh

#print axioms nativeOuterFieldCutoffAtScale_smooth
#print axioms exists_nativeOuter_cutoff_geometric_sender
end Yamabe3.Analysis.SpherePolar
