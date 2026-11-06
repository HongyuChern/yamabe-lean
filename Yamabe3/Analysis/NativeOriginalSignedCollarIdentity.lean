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


theorem nativeOriginalSignedEnergy_collar_identity
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (hF:ContDiffOn ℝ 2 F ({0}ᶜ:Set E))
    (hTF:EqOn (nativeH4GraphFunction (T₀ f)) F (closedBall (0:E) 4))
    (qi wo:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y) :
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    ∃wi wc:ℝ×SpherePolar.S→ℝ,Measurable wi ∧ Measurable wc ∧
      (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s Y.val) s wi) ∧
      (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s) s wc) ∧
      (toL2 g.leviCivitaData univ (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f):M→ℝ)
        =ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)]
          coordinateExtension e (fun x:E=>
            (ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z) (cylinderLift wo) (a⁻¹ • x)+
            (ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wc) (a⁻¹ • x)) ∧
      let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)+
        nativeTwoSidedInteriorJetCLM P hp v hv hb τ Y.val
      let K:=nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
        nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
      nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
        nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K := by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  obtain ⟨wi,wc,hwi,hwc,hi,ho,hE⟩:=W.model_field Y.val
  let u₀:E→ℝ:=(ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z) (cylinderLift wo)
  let u₁:E→ℝ:=(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wc)
  have hQb:(toL2 g.leviCivitaData univ (Q₀ f):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u₀ (a⁻¹ • x)):=by
    rw [hQ₀ f]
    exact nativeCompletedChartL2_same_function g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
      (L₀ f) (fun y=>χout (Real.exp S • y)*u₀ y) hL₀
  have hQc:(toL2 g.leviCivitaData univ (W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u₁ (a⁻¹ • x)):=by
    rw [W.native_field_class]
    exact nativeCompletedChartL2_same_function g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
      (W.LE Y.val) (fun y=>χout (Real.exp S • y)*u₁ y) hE
  have hbase:=nativeH4Matched_actual_matching P hp ht (T₀ f) (⟨F,hF⟩:nativeC2OffZero) hTF
  have hcorr:=nativeSupportedTwoSidedExteriorAllScale_matching P hp v hv hb b ht Y.val
  refine ⟨wi,wc,hwi,hwc,hi,ho,?_,?_⟩
  · let V:=e '' euclideanDilatedDomain a nativePoissonEntranceCollar
    have hV:IsOpen V:=e.isOpen_image_of_subset_source
      ((nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹))
      ((nativeActualFeedback_collar_fit W).trans hsource)
    filter_upwards [ae_restrict_of_ae (s:=V) (nativeOriginalSignedEnergyCLM_ae W T₀ Q₀ Rbase f),
      ae_restrict_of_ae (s:=V) hQb,ae_restrict_of_ae (s:=V) hQc,ae_restrict_mem hV.measurableSet] with y hz hb hc hy
    obtain ⟨x,hx,rfl⟩:=hy
    have hxK:=nativeActualFeedback_collar_fit W hx
    have hxS:=hsource hxK
    rw [hz,hb,hc,nativeActualFeedback_core_one W hx,sub_self,zero_mul,sub_zero]
    change nativeCompactChartFunction e (closedBall (0:E) R₀)
        (fun y:E=>χout (Real.exp S • (a⁻¹ • y))*u₀ (a⁻¹ • y)) (e x)+
      nativeCompactChartFunction e (closedBall (0:E) R₀)
        (fun y:E=>χout (Real.exp S • (a⁻¹ • y))*u₁ (a⁻¹ • y)) (e x)=
        coordinateExtension e (fun y:E=>u₀ (a⁻¹ • y)+u₁ (a⁻¹ • y)) (e x)
    rw [nativeCompactChartFunction,coordinateExtension_comp_apply e _ hxS,indicator_of_mem hxK,
      nativeCompactChartFunction,coordinateExtension_comp_apply e _ hxS,indicator_of_mem hxK,
      coordinateExtension_comp_apply e _ hxS,nativeActualFeedback_outer_cutoff_one W hx,one_mul,one_mul]
  · rw [map_add,map_add,map_add,map_add,nativeH4MatchedExteriorAllScale_zero]
    exact ⟨congrArg₂ (·+·) hbase.1 hcorr.1,congrArg₂ (·+·) hbase.2.1 hcorr.2.1⟩

#print axioms nativeOriginalSignedEnergy_collar_identity
end Yamabe3.Analysis.SpherePolar
