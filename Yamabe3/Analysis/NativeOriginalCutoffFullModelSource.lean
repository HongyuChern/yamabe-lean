import Yamabe3.Analysis.NativeOriginalOuterSameFieldOperator
import Yamabe3.Analysis.NativeOuterCutoffTestWindow
import Yamabe3.Analysis.NativeSupportedSourceCutoffIdentity

/-! Finite reconstruction of the COMPLETE actual exterior model source
on the cutoff test, then exact preservation of that SAME supported source.
This avoids imposing near-window support on the original physical test. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet

 theorem nativeSpectral_window_test_pairing (N:ℕ)
    (F G:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hG:∀ᵐt:ℝ∂volume,t∉Ioc (-(N:ℝ)/2) 0→G t=0):
    inner ℝ F G=∫t in Ioc (-(N:ℝ)/2) 0,inner ℝ (F t) (G t):=by
  rw [L2.inner_def,←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hG] with t ht
  by_cases htW:t∈Ioc (-(N:ℝ)/2) 0
  · rw [indicator_of_mem htW]
  · rw [indicator_of_notMem htW,ht htW,inner_zero_right]

 theorem nativeOriginalOuter_full_flat_pairing
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1) (b:ℝ) {τ:ℝ} (ht:0<τ)
    (N:ℕ) (x:HalfEndPhysicalH4Graph) (Y:NativeTwoSidedSource)
    (hY:∀ᵐt:ℝ∂volume,t<b→Y.2 t=0)
    (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hG:∀ᵐt:ℝ∂volume,t∉Ioc (-(N:ℝ)/2) 0→G t=0):
    (∑i:Fin N,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ))
        (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter i)+
          nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y (nativeOuterLogShellCenter i)).val)) G)=
      -(inner ℝ Y.2 G)+(∑i:Fin N,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeH4OuterComputedCompensationRow P ht b i x+
          nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y)) G):=by
  have hsource:(∑i:Fin N,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace (nativeOuterLogShellCenter i) Y.2))) G)=inner ℝ Y.2 G:=by
    have hh:=nativeFiniteOuterWindowSource_reconstructs N Y.2 G
    simp only [nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,sum_inner] at hh
    exact hh.trans (nativeSpectral_window_test_pairing N Y.2 G hG).symm
  simp only [Submodule.coe_add,map_add,inner_add_left]
  simp_rw [nativeH4Outer_flat_row_computed_compensation P ht b]
  simp only [nativeSupportedTwoSidedExteriorAllScaleJet]
  simp_rw [nativeSupportedOuter_shell_model_source b ht Y.2
    (nativeLowL2AngularCLM v hv hb Y.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb Y.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ Y) (nativeTwoSidedSourceSigma_regular P hp v hv hb τ Y) hY]
  simp only [inner_add_left,inner_neg_left,Finset.sum_add_distrib,Finset.sum_neg_distrib,
    nativeFiniteWindowOuterCompensationRow,hsource]
  ring

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)


 theorem nativeOriginalAffine_cutoff_model_full_source
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (hsφ:tsupport φ⊆{y:E|1<‖y‖}):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
    let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    (∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ))
        (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter i)+
          nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val (nativeOuterLogShellCenter i)).val))
        (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ))=
      -(inner ℝ Y.val.2 (nativePhysicalPairTestL2 φ hφ hc h0))+
      (∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeH4OuterComputedCompensationRow P ht b i x+
          nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ)):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
  have hYs:∀ᵐt:ℝ∂volume,t<b→Y.val.2 t=0:=(nativeSupportedSourcePairSpace_mem_iff b Y.val).mp Y.property
  have hh:=nativeOriginalOuter_full_flat_pairing P hp v hv hb b ht (m+n) x Y.val hYs _
    (nativeOuterCutoff_spectral_test_window χout hχout W.outer_support φ hφ hc h0 hsφ W.far_window)
  have hsource:=nativeSupportedSource_cutoff_test_pairing hχout W.outer_plateau W.source_cutoff Y.val.2 hYs φ hφ hc h0
  dsimp only at hh hsource
  rw [hsource] at hh
  exact hh

#print axioms nativeSpectral_window_test_pairing
#print axioms nativeOriginalOuter_full_flat_pairing
#print axioms nativeOriginalAffine_cutoff_model_full_source
end Yamabe3.Analysis.SpherePolar
