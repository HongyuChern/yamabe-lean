import Yamabe3.Analysis.NativeOriginalFullOuterJacobianPairing
import Yamabe3.Analysis.NativeBCFPhysicalRowPairing
import Yamabe3.Analysis.NativeH4CorrectedExteriorAllScale

/-! ONE actual original baseline-plus-affine-correction exterior field
supplies every full weak operator row. It is fixed before all scales and
tests. Its volume class is not replaced by an unrelated H4 extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet

 theorem nativeOriginalFullOuterRow_same_jet
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0≤v t ∧ v t≤1) (b:ℝ) {τ:ℝ} (ht:0<τ)
    (gE:RiemannianMetric 3 E) (a:ℝ) (n:ℕ) (x:HalfEndPhysicalH4Graph) (Y:NativeTwoSidedSource):
    nativeH4OuterFullJacobianRow P hp ht gE a n x+
      nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht gE a n Y=
    (nativeFlatCollarJetCLM (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))+
      nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter n))
        (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ)))
      (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter n)+
        nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y (nativeOuterLogShellCenter n)).val:=by
  rw [nativeH4OuterFullJacobianRow,nativeFiniteWindowOuterJacobianRow,
    nativeH4FiniteWindowGeometricRow_same_field,nativeFiniteWindowGeometricRow_same_field]
  change _=(nativeFlatCollarJetCLM _+nativeBCFCollarErrorCLM _ _ _)
    (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter n)+
      nativeFiniteWindowOuterJet P hp v hv hb b ht (nativeOuterLogShellCenter n) Y).val
  simp only [Submodule.coe_add,map_add,ContinuousLinearMap.add_apply]
  abel

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


 theorem exists_nativeOriginal_outer_same_field_operator
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧
      (∀s:ℝ,NativeScaledJetRep
        (nativeH4MatchedExteriorAllScaleJet P ht x s+
          nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s) s w) ∧
      ∀(i:ℕ)(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)(hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
          (nativeH4OuterFullJacobianRow P hp ht gE a i x+
            nativeFiniteWindowOuterJacobianRow P hp v hv hb b ht gE a i Y.val))
          (nativePhysicalPairTestL2 φ hφ hc h0)=
        ∫y in nativeScaledSourceShell (nativeOuterLogShellCenter i),
          (nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow (nativeOuterLogShellCenter i)) gE a
            (fun _=>0) 0 (cylinderLift w) y-
            gE.pullbackVolumeDensity id (a • y)*nativeHalfEndPotentialCoefficient (fullBubblePhasePotential τ) y*cylinderLift w y)*φ y:=by
  dsimp only
  let T:HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource:=
    (nativeSupportedSourcePairSpace b).subtypeL.comp
      (nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase)
  obtain ⟨w,hw,hjet⟩:=exists_nativeH4CorrectedExteriorAllScale_same_field P hp v hv hb b ht T x
  have hj(s:ℝ):NativeScaledJetRep
      (nativeH4MatchedExteriorAllScaleJet P ht x s+
        nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (T x) s) s w:=hjet s
  refine ⟨w,hw,hj,fun i φ hφ hc h0=>?_⟩
  rw [nativeOriginalFullOuterRow_same_jet]
  exact nativeBCF_same_field_shell_pairing gE a (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ)
    (nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter i)+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (T x) (nativeOuterLogShellCenter i))
    (hj (nativeOuterLogShellCenter i)) φ hφ hc h0

#print axioms nativeOriginalFullOuterRow_same_jet
#print axioms exists_nativeOriginal_outer_same_field_operator
end Yamabe3.Analysis.SpherePolar
