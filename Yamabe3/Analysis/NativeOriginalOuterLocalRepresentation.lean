import Yamabe3.Analysis.NativeOriginalSignedOuterGlobalClass

/-! The actual baseline-plus-correction completion has the SAME local
outer H2 coordinate representative. The signed return is cancelled only
in an identity of completion classes; no boundary restriction of a
volume a.e. identity is made. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
attribute [local instance] Classical.propDecidable
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

 theorem nativeOriginalSameOuter_completed_local_representation
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (qi wo w:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y)
    (hwo:∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s) s wo)
    (hw:∀s:ℝ,NativeScaledJetRep
      (nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s+
        nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht
          (nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)).val s) s w)
    (vaux:E→ℝ)
    (hAux:EqOn vaux (fun y=>χout (Real.exp S • y)*cylinderLift w y)
      (nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0)))
    (A:Set E) (hA:IsOpen A) (hAK:A⊆closedBall (0:E) R₀)
    (hAunit:∀x∈A,a⁻¹ • x∈nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0) ∧ 1<‖a⁻¹ • x‖):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    (toL2 g.leviCivitaData univ (Q₀ f+W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' A)]
      coordinateExtension e (fun y:E=>vaux (a⁻¹ • y)):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  obtain ⟨wi,hwi,hij,hZ⟩:=nativeOriginalSignedEnergy_same_outer_global_class W T₀ Q₀ Rbase O L₀ hQ₀
    f F qi wo w hL₀ hwo hw
  have hQadd:(toL2 g.leviCivitaData univ (Q₀ f+W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure]
      (fun y=>toL2 g.leviCivitaData univ (Q₀ f) y+toL2 g.leviCivitaData univ (W.Q Y.val) y):=by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hQ:(toL2 g.leviCivitaData univ (Q₀ f+W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure]
      (fun y=>nativeCompactChartFunction e (closedBall (0:E) R₀)
        (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*
          (ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z+cylinderLift wi z) (cylinderLift w) (a⁻¹ • x)) y):=by
    filter_upwards [hQadd,hZ,nativeOriginalSignedEnergyCLM_ae W T₀ Q₀ Rbase f] with y hq hz hs
    linear_combination hq+hz-hs
  have hAs:A⊆e.source:=hAK.trans hsource
  have hΩ:IsOpen (e '' A):=e.isOpen_image_of_subset_source hA hAs
  filter_upwards [ae_restrict_of_ae (s:=e '' A) hQ,ae_restrict_mem hΩ.measurableSet] with y hy hyA
  obtain ⟨x,hx,rfl⟩:=hyA
  have hxunit:1<‖a⁻¹ • x‖:=(hAunit x hx).2
  have hxB:a⁻¹ • x∉ball (0:E) 1:=fun h=>not_lt_of_ge hxunit.le (mem_ball_zero_iff.mp h)
  rw [hy,nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hAs hx),
    coordinateExtension_comp_apply e _ (hAs hx),indicator_of_mem (hAK hx),piecewise_eq_of_notMem _ _ _ hxB]
  exact (hAux (hAunit x hx).1).symm

#print axioms nativeOriginalSameOuter_completed_local_representation
end Yamabe3.Analysis.SpherePolar
