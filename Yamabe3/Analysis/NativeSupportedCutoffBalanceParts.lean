import Yamabe3.Analysis.NativeOriginalCutoffFullModelSource
import Yamabe3.Analysis.NativeOriginalCutoffNearParts
import Yamabe3.Analysis.NativeRemoteReturnResponse
import Yamabe3.Analysis.NativeOriginalAffineFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The actual affine fixed equation cancels the COMPLETE source against
its finite near geometric rows on EVERY spectral test. No near-window
support hypothesis on the test is imposed or inferred. The same total
return remains on the right-hand side. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
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


 theorem nativeSupported_actual_all_test_source_cancellation
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hFix:Y.val=nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a Y.val-(W.I R).val)
    (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ)):
    -(inner ℝ Y.val.2 G)+
      (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht gE a i Y.val)) G)=
      inner ℝ (W.I R).val.2 G:=by
  have hh:=congrArg (fun X:NativeTwoSidedSource=>inner ℝ X.2 G) hFix
  change inner ℝ Y.val.2 G=inner ℝ ((_)-(W.I R).val.2) G at hh
  rw [inner_sub_left] at hh
  simp only [nativeFiniteWindowGlobalSourceCLM,nativeFiniteOuterWindowSourceCLM,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,sum_inner] at hh
  linarith only [hh]

 include W in
 theorem nativeSupported_cutoff_model_full_source
    (Y:nativeSupportedSourcePairSpace b)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (hsφ:tsupport φ⊆{y:E|1<‖y‖}):
    let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
    let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    (∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ))
        (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val (nativeOuterLogShellCenter i)).val))
        (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ))=
      -(inner ℝ Y.val.2 (nativePhysicalPairTestL2 φ hφ hc h0))+
      (∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ)):=by
  dsimp only
  have hYs:∀ᵐt:ℝ∂volume,t<b→Y.val.2 t=0:=(nativeSupportedSourcePairSpace_mem_iff b Y.val).mp Y.property
  have hh:=nativeOriginalOuter_full_flat_pairing P hp v hv hb b ht (m+n) 0 Y.val hYs _
    (nativeOuterCutoff_spectral_test_window χout hχout W.outer_support φ hφ hc h0 hsφ W.far_window)
  have hsource:=nativeSupportedSource_cutoff_test_pairing hχout W.outer_plateau W.source_cutoff Y.val.2 hYs φ hφ hc h0
  dsimp only at hh hsource
  rw [hsource] at hh
  have hj0(i:ℕ):nativeH4MatchedExteriorAllScaleJet P ht 0 (nativeOuterLogShellCenter i)=0:=by
    obtain ⟨D,hD,hhJ⟩:=exists_nativeH4MatchedExteriorAllScale_bound P ht
    have hs:nativeOuterLogShellCenter i≤0:=by dsimp only [nativeOuterLogShellCenter];have hi:0≤(i:ℝ):=Nat.cast_nonneg _;linarith
    obtain ⟨J,hJ,hJv⟩:=hhJ (nativeOuterLogShellCenter i) hs
    exact (hJv 0).symm.trans J.map_zero
  have hComp0(i:ℕ):nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeH4OuterComputedCompensationRow P ht b i 0)=0:=by
    rw [←nativeH4Outer_flat_row_computed_compensation P ht b i 0,hj0]
    simp only [ZeroMemClass.coe_zero,map_zero]
  simpa only [hj0,zero_add,map_add,hComp0,inner_add_left,inner_zero_left] using hh

 include W in
 theorem nativeSupported_near_cutoff_geometry (Y:nativeSupportedSourcePairSpace b) (i:Fin m):
    let s:=nativeOuterLogShellCenter i
    let V:=boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)
    let J:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s
    nativeFullShellSourceReturnCLM s (nativeBCFCollarErrorCLM gE (a*Real.exp (-s)) V
      (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χout)
        (nativeOuterFieldCutoffAtScale_smooth S s hχout) J).val)=
      nativeFullShellSourceReturnCLM s (nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht gE a i Y.val):=by
  dsimp only
  rw [nativeGeometricCutoffPlateau_shell_return gE (mul_pos ha (Real.exp_pos _)) _ _ _
    (nativeNearOuterCutoff_shell_plateau W.outer_plateau W.near_support W.source_cutoff i)]
  rw [nativeFiniteWindowGeometricRow_same_field]
  rfl

#print axioms nativeSupported_actual_all_test_source_cancellation
#print axioms nativeSupported_cutoff_model_full_source
#print axioms nativeSupported_near_cutoff_geometry
end Yamabe3.Analysis.SpherePolar
