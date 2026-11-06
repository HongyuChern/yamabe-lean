import Yamabe3.Analysis.NativeOriginalAffineOuterPairing
import Yamabe3.Analysis.NativeH4OuterSupportedIdentity

/-! The SAME baseline-plus-correction field has a full native exterior
shell Jacobian. Its actual affine feedback cancels every near geometric
row, leaving its computed four low compensations and SAME incoming return.
No vanishing residual is inferred from a norm estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet

 def nativeH4OuterComputedCompensationRow (P:NativeHighPotential) {τ:ℝ} (ht:0<τ)
    (b:ℝ) (n:ℕ) (x:HalfEndPhysicalH4Graph):NativeCollarL2:=
  nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))
    (nativeSupportedLowCauchyAllScaleJet b ht 0 (nativeH4GraphAngularValueCLM x)
      (nativeH4GraphAngularNormalCLM x) (nativeOuterLogShellCenter n)).val

 def nativeH4OuterFullJacobianRow (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    {τ:ℝ} (ht:0<τ) (gE:RiemannianMetric 3 E) (a:ℝ) (n:ℕ) (x:HalfEndPhysicalH4Graph):NativeCollarL2:=
  nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))
    (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter n)).val+
      nativeH4FiniteWindowGeometricRowCLM P ht gE a n x

 theorem nativeH4Outer_flat_row_computed_compensation
    (P:NativeHighPotential) {τ:ℝ} (ht:0<τ) (b:ℝ) (n:ℕ) (x:HalfEndPhysicalH4Graph):
    nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n)
      (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))
        (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter n)).val)=
      nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter n) (nativeH4OuterComputedCompensationRow P ht b n x):=by
  have hz:∀ᵐt:ℝ∂volume,t<b→(0:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) t=0:=by
    filter_upwards [Lp.coeFn_zero AngularSpectralSpace 2 (volume:Measure ℝ)] with t ht
    exact fun _=>ht
  have hh:=nativeSupportedOuter_shell_model_source b ht 0 (nativeH4GraphAngularValueCLM x)
    (nativeH4GraphAngularNormalCLM x) (nativeH4GraphExteriorDatumCLM (fullBubbleHighPotential (-τ)) P x)
    (nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P x) hz n
  dsimp only at hh
  rw [←nativeH4MatchedExteriorAllScale_supported_zero P ht b x] at hh
  simpa only [map_zero,neg_zero,zero_add,nativeH4OuterComputedCompensationRow] using hh

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


 theorem nativeOriginalAffine_full_outer_Jacobian_pairing
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hG:∀ᵐt:ℝ∂volume,t∉Ioc (-(m:ℝ)/2) 0→G t=0):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeH4OuterFullJacobianRow P hp ht gE a i x+
        nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht gE a i Y.val)) G)=
      (∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeH4OuterComputedCompensationRow P ht b i x+
          nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) G)+
      inner ℝ (W.I R).val.2 G:=by
  dsimp only
  have hh:=nativeOriginalAffineFeedback_outer_residual_pairing W Rbase x G hG
  simp only [nativeH4FiniteWindowGlobalSourceCLM,nativeFiniteOuterWindowSourceCLM,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,sum_inner] at hh
  simp only [map_add,inner_add_left,Finset.sum_add_distrib,nativeH4OuterFullJacobianRow]
  simp only [map_add,inner_add_left,nativeH4Outer_flat_row_computed_compensation P ht b,Finset.sum_add_distrib]
  linarith only [hh]

#print axioms nativeH4Outer_flat_row_computed_compensation
#print axioms nativeOriginalAffine_full_outer_Jacobian_pairing
end Yamabe3.Analysis.SpherePolar
