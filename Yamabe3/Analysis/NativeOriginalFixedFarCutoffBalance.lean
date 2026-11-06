import Yamabe3.Analysis.NativeOriginalCutoffNearParts
import Yamabe3.Analysis.NativeOriginalCutoffFullModelSource
import Yamabe3.Analysis.NativeOuterCutoffDualPairing
import Yamabe3.Analysis.NativeCommutatorSpectralAssembly
import Yamabe3.Analysis.NativeOriginalFiniteCutoffBalance

/-! Complete finite cutoff operator balance for the actual original
source feedback. Every near geometric row is cancelled on the ORIGINAL
test, leaving only the computed four compensations, same incoming return,
and genuine far commutator/geometric rows. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
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

 theorem nativeOriginalAffine_fixed_far_cutoff_balance
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (x:HalfEndPhysicalH4Graph) (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ)
    (hsφ:tsupport φ⊆{y:E|1<‖y‖}):
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
    (∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      ((nativeFlatCollarJetCLM (Vs i)+nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter i)) (Vs i)) (cut i).val)) G)=
      (∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
        (nativeH4OuterComputedCompensationRow P ht b i x+
          nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) (nativePhysicalPairTestL2 ψ hψ hcψ h0ψ))+
      inner ℝ (W.I R).val.2 G+
      inner ℝ (nativeFullShellSourceReturnCLM S (nativeCollarCutoffCommutatorCLM χout hχout
        (nativeH4MatchedExteriorAllScaleJet P ht x S+
          nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val S).val)) G+
      (∑i:Fin n,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter (m+i.val))
        (nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter (m+i.val))) (Vs (m+i.val)) (cut (m+i.val)).val)) G):=by
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
  let flat:ℕ→ℝ:=fun i=>inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    (nativeFlatCollarJetCLM (Vs i) (J i).val)) Gψ
  let comm:ℕ→ℝ:=fun i=>inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χout)
      (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχout) (J i).val)) G
  let geo:ℕ→ℝ:=fun i=>inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    (nativeBCFCollarErrorCLM gE (a*Real.exp (-nativeOuterLogShellCenter i)) (Vs i) (cut i).val)) G
  let comp:ℝ:=∑i:Fin (m+n),inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
    (nativeH4OuterComputedCompensationRow P ht b i x+
      nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val)) Gψ
  let CS:=inner ℝ (nativeFullShellSourceReturnCLM S (nativeCollarCutoffCommutatorCLM χout hχout
    (nativeH4MatchedExteriorAllScaleJet P ht x S+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val S).val)) G
  change (∑i:Fin (m+n),full i)=comp+inner ℝ (W.I R).val.2 G+CS+(∑i:Fin n,geo (m+i.val))
  have hbal:(∑i:Fin (m+n),full i)=comp+inner ℝ (W.I R).val.2 G+
      (∑i:Fin n,comm (m+i.val))+(∑i:Fin n,geo (m+i.val)):=
    nativeOriginalAffine_finite_cutoff_balance W Rbase x φ hφ hc h0 hsφ
  obtain ⟨w,hw,hjet,hrows⟩:=exists_nativeOriginal_outer_same_field_operator W Rbase x
  have hcomm:(∑i:Fin (m+n),comm i)=CS:=
    nativeAllScale_cutoff_commutator_spectral_assembly _ (cylinderLift w) hjet χout hχout W.outer_derivatives S (m+n)
      (by linarith [W.far_scale]) (by linarith [W.far_window]) φ hφ hc h0
  have hnear(i:Fin m):comm i=0:=by
    change inner ℝ _ G=0
    rw [nativeOriginalAffine_near_cutoff_commutator_zero W Rbase x i,inner_zero_left]
  have hsplit:(∑i:Fin (m+n),comm i)=(∑i:Fin n,comm (m+i.val)):=by
    rw [Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd,hnear,Finset.sum_const_zero,zero_add]
  have hfarcomm:(∑i:Fin n,comm (m+i.val))=CS:=hsplit.symm.trans hcomm
  rw [hfarcomm] at hbal
  exact hbal

#print axioms nativeOriginalAffine_fixed_far_cutoff_balance
end Yamabe3.Analysis.SpherePolar
