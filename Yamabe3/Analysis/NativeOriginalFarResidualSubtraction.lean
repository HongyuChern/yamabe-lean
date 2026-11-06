import Yamabe3.Analysis.NativeOriginalFixedFarCutoffBalance
import Yamabe3.Analysis.NativeOriginalReturnSpectralPairing

/-! Exact cancellation of the ACTUAL total far return against the
complete finite cutoff operator. Both equations concern the SAME
source, field, native test and returned completion element. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096
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


 theorem nativeOriginalAffine_actual_far_residual_subtraction
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hfar:NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase)
    (x:HalfEndPhysicalH4Graph) (η:EnergyTest g.leviCivitaData univ)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (hsφ:tsupport φ⊆{y:E|1<‖y‖})
    (htest:∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y)):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
    let J:ℕ→nativeCollarJetClosure:=fun i=>nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter i)+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val (nativeOuterLogShellCenter i)
    let Vs:ℕ→ℝ→ᵇℝ:=fun i=>boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ)
    let cut:ℕ→nativeCollarJetClosure:=fun i=>nativeCollarCutoffCLM
      (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout) (J i)
    let G:=nativePhysicalPairTestL2 φ hφ hc h0
    let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
    let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
    let hcψ:HasCompactSupport ψ:=hc.mul_left
    let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
    8*a*(∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      ((nativeFlatCollarJetCLM (Vs i)+nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter i)) (Vs i)) (cut i).val)) G)-
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val (η:H1Zero g.leviCivitaData univ)=
      8*a*(∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeH4OuterComputedCompensationRow P ht b i x+
          nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ))+
      8*a*inner ℝ (W.I R).val.2 G-
      (∫y,8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
        toL2 g.leviCivitaData univ R.val y)*η y ∂g.volumeMeasure):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
  let R:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase x
  let J:ℕ→nativeCollarJetClosure:=fun i=>nativeH4MatchedExteriorAllScaleJet P ht x (nativeOuterLogShellCenter i)+
    nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val (nativeOuterLogShellCenter i)
  let Vs:ℕ→ℝ→ᵇℝ:=fun i=>boundedTimeTranslate ℝ (nativeOuterLogShellCenter i) (fullBubblePhasePotential τ)
  let cut:ℕ→nativeCollarJetClosure:=fun i=>nativeCollarCutoffCLM
    (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
    (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout) (J i)
  let G:=nativePhysicalPairTestL2 φ hφ hc h0
  let ψ:E→ℝ:=fun y=>χout (Real.exp S • y)*φ y
  let hψ:ContDiff ℝ ∞ ψ:=(hχout.comp (contDiff_id.const_smul _)).mul hφ
  let hcψ:HasCompactSupport ψ:=hc.mul_left
  let h0ψ:(0:E)∉tsupport ψ:=fun h=>h0 (tsupport_mul_subset_right h)
  let Gψ:=nativePhysicalPairTestL2 ψ hψ hcψ h0ψ
  let full:ℕ→ℝ:=fun i=>inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    ((nativeFlatCollarJetCLM (Vs i)+nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter i)) (Vs i)) (cut i).val)) G
  let geo:ℕ→ℝ:=fun i=>inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    (nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter i)) (Vs i) (cut i).val)) G
  let comp:ℝ:=∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    (nativeH4OuterComputedCompensationRow P ht b i x+
      nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) Gψ
  let CS:=inner ℝ (nativeFullShellSourceReturnCLM S (nativeCollarCutoffCommutatorCLM χout hχout
    (nativeH4MatchedExteriorAllScaleJet P ht x S+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val S).val)) G
  let tail:ℝ:=∫y,8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
    toL2 g.leviCivitaData univ R.val y)*η y ∂g.volumeMeasure
  change 8*a*(∑i:Fin (m+n),full i)-closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val (η:H1Zero g.leviCivitaData univ)=
    8*a*comp+8*a*inner ℝ (W.I R).val.2 G-tail
  have hbal:(∑i:Fin (m+n),full i)=comp+inner ℝ (W.I R).val.2 G+CS+(∑i:Fin n,geo (m+i.val)):=
    nativeOriginalAffine_fixed_far_cutoff_balance W Rbase x φ hφ hc h0 hsφ
  have hret:closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const R.val (η:H1Zero g.leviCivitaData univ)=
      8*a*CS+8*a*(∑i:Fin n,geo (m+i.val))+tail:=
    nativeOriginalAffineReturn_actual_spectral_pairing W hcoeff hfit Rbase hfar x η φ hφ hc h0 htest
  linear_combination 8*a*hbal-hret

#print axioms nativeOriginalAffine_actual_far_residual_subtraction
end Yamabe3.Analysis.SpherePolar
