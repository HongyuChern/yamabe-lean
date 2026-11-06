import Yamabe3.Analysis.NativeOriginalAllTestSourceCancellation
import Yamabe3.Analysis.NativeNearCutoffPlateau
import Yamabe3.Analysis.NativeCutoffPlateauSourceParts
import Yamabe3.Analysis.NativeOriginalOuterSameFieldOperator

/-! Actual near cutoff geometry and commutators, before any test support
restriction. The same affine source cancels on every spectral test. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
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

 theorem nativeOriginalAffine_near_cutoff_geometry
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (i:Fin m):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let s:=nativeOuterLogShellCenter i
    let V:=boundedTimeTranslate ℝ s (fullBubblePhasePotential τ)
    let J:=nativeH4MatchedExteriorAllScaleJet P ht x s+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s
    nativeFullShellSourceReturnCLM s (nativeBCFCollarErrorCLM gE (a*Real.exp (-s)) V
      (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S s χout)
        (nativeOuterFieldCutoffAtScale_smooth S s hχout) J).val)=
      nativeFullShellSourceReturnCLM s (nativeH4FiniteWindowGeometricRowCLM P ht gE a i x+
        nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht gE a i Y.val):=by
  dsimp only
  rw [nativeGeometricCutoffPlateau_shell_return gE (mul_pos ha (Real.exp_pos _)) _ _ _
    (nativeNearOuterCutoff_shell_plateau W.outer_plateau W.near_support W.source_cutoff i)]
  rw [nativeH4FiniteWindowGeometricRow_same_field,nativeFiniteWindowGeometricRow_same_field]
  simp only [Submodule.coe_add,map_add,nativeFiniteWindowOuterJet,nativeSupportedTwoSidedExteriorAllScaleJet]

 theorem nativeOriginalAffine_near_cutoff_commutator_zero
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (i:Fin m):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let s:=nativeOuterLogShellCenter i
    let J:=nativeH4MatchedExteriorAllScaleJet P ht x s+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s
    nativeFullShellSourceReturnCLM s (nativeCollarCutoffCommutatorCLM
      (nativeOuterFieldCutoffAtScale S s χout)
      (nativeOuterFieldCutoffAtScale_smooth S s hχout) J.val)=0:=by
  dsimp only
  exact nativeCutoffPlateau_commutator_return_zero _ _
    (nativeNearOuterCutoff_shell_plateau W.outer_plateau W.near_support W.source_cutoff i) _ _

 theorem nativeOriginalAffine_near_cutoff_all_test_cancellation
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ)):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    (-(inner ℝ Y.val.2 G)+(∑i:Fin m,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter i))
        (boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ))
        (nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
          (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout)
          (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter i)+
            nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val (nativeOuterLogShellCenter i))).val)) G))=
      inner ℝ (W.I R).val.2 G:=by
  dsimp only
  simp_rw [nativeOriginalAffine_near_cutoff_geometry W Rbase x]
  exact nativeOriginalAffine_all_test_source_cancellation W Rbase x G

#print axioms nativeOriginalAffine_near_cutoff_geometry
#print axioms nativeOriginalAffine_near_cutoff_commutator_zero
#print axioms nativeOriginalAffine_near_cutoff_all_test_cancellation
end Yamabe3.Analysis.SpherePolar
