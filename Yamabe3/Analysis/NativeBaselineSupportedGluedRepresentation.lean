import Yamabe3.Analysis.NativeRestrictedChartAeTransport
import Yamabe3.Analysis.NativeBaselineSupportedIdentity
import Yamabe3.Analysis.NativeSupportedSignedEnergy
import Yamabe3.Analysis.NativeOriginalSignedInnerIdentity
import Yamabe3.Analysis.NativeOriginalSignedEnergy
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization
import Yamabe3.Analysis.NativeActualFeedbackLocalGreen

/-! The same SIGNED original-source completed field agrees with the
sum of its actual baseline and correction on the entire physical collar.
The shared return cancels there by the actual core plateau. The literal
baseline/correction jets retain matching value and normal traces. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
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


theorem nativeBaselineSupportedSigned_glued_representation
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (hF:ContDiffOn ℝ 2 F ({0}ᶜ:Set E))
    (hTF:EqOn (nativeH4GraphFunction (T₀ f)) F (closedBall (0:E) 4))
    (qi wo:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y)
    (hBi:((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)).val.1:E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]fun x=>F x+cylinderLift qi x)
    (hBo:((nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0).val.1:E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift wo):
    let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)+
      nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
    let K:=nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
    (toL2 g.leviCivitaData univ (Q₀ f+nativeSupportedSignedEnergy W Y R):M→ℝ)
      =ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)]
        coordinateExtension e (fun x:E=>nativeCollarGluedFunction J.val.1 K.val.1 (a⁻¹ • x)) ∧
    nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
    nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K:=by
  dsimp only
  let Ji:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)
  let Ki:=nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
  let Jo:=nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0
  let Ko:=nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
  obtain ⟨wi,wc,hwi,hwc,hci,hco,hrep,hm⟩:=nativeBaselineSupportedSigned_collar_identity W
    T₀ Q₀ Y R O L₀ hQ₀ f F hF hTF qi wo hL₀
  have hi:(Ki.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift wi:=by
    simpa only [NativeScaledJetRep,nativeTwoSidedAllScale_zero,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] using hci 0
  have ho:(Ko.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]cylinderLift wc:=by
    simpa only [NativeScaledJetRep,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] using hco 0
  have hEu:(fun x:E=>(ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z) (cylinderLift wo) x+
      (ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wc) x)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeCollarGluedFunction (Ji+Ki).val.1 (Jo+Ko).val.1:=by
    filter_upwards [hBi,hBo,hi,ho,Lp.coeFn_add Ji.val.1 Ki.val.1,Lp.coeFn_add Jo.val.1 Ko.val.1] with x hbi hbo hi ho hai hao
    by_cases hx:x∈ball (0:E) 1
    · simp only [nativeCollarGluedFunction,piecewise_eq_of_mem _ _ _ hx]
      change F x+cylinderLift qi x+cylinderLift wi x=(Ji.val.1+Ki.val.1:NativeCollarL2) x
      rw [hai]
      change F x+cylinderLift qi x+cylinderLift wi x=Ji.val.1 x+Ki.val.1 x
      rw [hbi,hi]
    · simp only [nativeCollarGluedFunction,piecewise_eq_of_notMem _ _ _ hx]
      change cylinderLift wo x+cylinderLift wc x=(Jo.val.1+Ko.val.1:NativeCollarL2) x
      rw [hao]
      change cylinderLift wo x+cylinderLift wc x=Jo.val.1 x+Ko.val.1 x
      rw [hbo,ho]
  have hd:=ae_comp_dilation (inv_ne_zero ha.ne') hEu
  have hD:IsOpen (euclideanDilatedDomain a nativePoissonEntranceCollar):=
    (nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹)
  have hn:=coordinateExtension_congr_restricted_volume_ae g e he hei hD
    ((nativeActualFeedback_collar_fit W).trans hsource) hd
  exact ⟨hrep.trans hn,hm⟩

#print axioms nativeBaselineSupportedSigned_glued_representation
end Yamabe3.Analysis.SpherePolar
