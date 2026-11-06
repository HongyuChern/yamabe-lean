import Yamabe3.Analysis.NativeOriginalSignedCollarIdentity
import Yamabe3.Analysis.NativeAllScaleFieldUniqueness

/-! The ACTUAL signed original-source native completion uses any already
identified SAME all-scale exterior representative. Its complete global
volume class, outer cutoff, actual inner field and same return are kept.
No volume equality is restricted to a hypersurface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option profiler true
set_option profiler.threshold 1500
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


theorem nativeOriginalSignedEnergy_same_outer_global_class
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
          (nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)).val s) s w):
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    ∃wi:ℝ×SpherePolar.S→ℝ,Measurable wi ∧
      (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s Y.val) s wi) ∧
      (toL2 g.leviCivitaData univ (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f):M→ℝ)=ᵐ[g.volumeMeasure]
        (fun y=>nativeCompactChartFunction e (closedBall (0:E) R₀)
          (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*
            (ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z+cylinderLift wi z) (cylinderLift w) (a⁻¹ • x)) y-
          (1-W.core y)*toL2 g.leviCivitaData univ
            (nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)).val y):=by
  dsimp only
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  obtain ⟨wi,wc,hwi,hwc,hi,ho,hE⟩:=W.model_field Y.val
  have hsum:cylinderLift (fun p=>wo p+wc p)=ᵐ[volume]cylinderLift w:=by
    apply native_all_scale_jet_same_volume_class
      (fun s=>nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s+
        nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s)
      (fun s=>(hwo s).add (ho s)) hw
  rw [native_cylinderLift_add] at hsum
  let u₀:E→ℝ:=(ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z) (cylinderLift wo)
  let u₁:E→ℝ:=(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wc)
  let u:E→ℝ:=(ball (0:E) 1).piecewise (fun z=>F z+cylinderLift qi z+cylinderLift wi z) (cylinderLift w)
  have hu:(fun x:E=>u₀ x+u₁ x)=ᵐ[volume]u:=by
    filter_upwards [hsum] with x hx
    by_cases hxB:x∈ball (0:E) 1
    · simp only [u₀,u₁,u,piecewise_eq_of_mem _ _ _ hxB]
    · simp only [u₀,u₁,u,piecewise_eq_of_notMem _ _ _ hxB]
      exact hx
  let f₀:E→ℝ:=fun x=>χout (Real.exp S • (a⁻¹ • x))*u₀ (a⁻¹ • x)
  let f₁:E→ℝ:=fun x=>χout (Real.exp S • (a⁻¹ • x))*u₁ (a⁻¹ • x)
  have hud:=(ae_comp_dilation (inv_ne_zero ha.ne') (ae_restrict_of_ae (s:=univ) hu))
  simp only [preimage_univ,Measure.restrict_univ] at hud
  have hcoord:(fun x:E=>f₀ x+f₁ x)=ᵐ[volume]
      (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u (a⁻¹ • x)):=by
    filter_upwards [hud] with x hx
    change χout (Real.exp S • (a⁻¹ • x))*u₀ (a⁻¹ • x)+
      χout (Real.exp S • (a⁻¹ • x))*u₁ (a⁻¹ • x)=_
    rw [←mul_add,hx]
  have hnat:=nativeCompactChart_congr_volume_ae g e he hei (isCompact_closedBall (0:E) R₀).measurableSet
    (ae_restrict_of_ae (s:=closedBall (0:E) R₀) hcoord)
  have hQb:(toL2 g.leviCivitaData univ (Q₀ f):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) f₀:=by
    rw [hQ₀ f]
    exact nativeCompletedChartL2_same_function g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
      (L₀ f) (fun y=>χout (Real.exp S • y)*u₀ y) hL₀
  have hQc:(toL2 g.leviCivitaData univ (W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) f₁:=by
    rw [W.native_field_class]
    exact nativeCompletedChartL2_same_function g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
      (W.LE Y.val) (fun y=>χout (Real.exp S • y)*u₁ y) hE
  refine ⟨wi,hwi,hi,?_⟩
  filter_upwards [nativeOriginalSignedEnergyCLM_ae W T₀ Q₀ Rbase f,hQb,hQc,hnat] with y hz hb hc hn
  rw [hz,hb,hc]
  have hadd:=congrFun ((nativeCompactChartFunctionLinear e (closedBall (0:E) R₀)).map_add f₀ f₁) y
  change nativeCompactChartFunction e (closedBall (0:E) R₀) (fun x=>f₀ x+f₁ x) y=
    nativeCompactChartFunction e (closedBall (0:E) R₀) f₀ y+nativeCompactChartFunction e (closedBall (0:E) R₀) f₁ y at hadd
  rw [←hadd,hn]

#print axioms nativeOriginalSignedEnergy_same_outer_global_class
end Yamabe3.Analysis.SpherePolar
