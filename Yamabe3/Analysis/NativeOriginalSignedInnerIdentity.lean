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


include W in
theorem nativeActualFeedback_inner_ball_fit :
    euclideanDilatedDomain a (ball (0:E) 1)⊆closedBall (0:E) R₀ := by
  apply euclideanDilatedBall_subset_closedBall ha
  have hh:=W.receiving_fit
  linarith

theorem nativeActualFeedback_core_one_inner {x:E}
    (hx:x∈euclideanDilatedDomain a (ball (0:E) 1)) : W.core (e x)=1 := by
  have hxS:=hsource (nativeActualFeedback_inner_ball_fit W hx)
  have he:a • (a⁻¹ • x)=x:=by rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have hv:=W.core_value (a⁻¹ • x) (by simpa only [he] using hxS)
  rw [he] at hv
  have hn:‖a⁻¹ • x‖<1:=mem_ball_zero_iff.mp hx
  exact hv.trans ((W.inner_plateau _ (by rw [mem_closedBall,dist_zero_right];linarith)).self_of_nhds)

include W in
theorem nativeActualFeedback_outer_cutoff_one_inner {x:E} (hx:x∈ball (0:E) 1) :
    χout (Real.exp S • x)=1 := by
  have hn:=mem_ball_zero_iff.mp hx
  have hs:‖Real.exp S • x‖≤Real.exp (-(1/8:ℝ)):=by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le hn.le).trans
      (Real.exp_le_exp.mpr (by linarith [W.far_scale]))
  exact (W.outer_plateau _ (by simpa only [mem_closedBall,dist_zero_right] using hs)).self_of_nhds

theorem nativeOriginalSignedEnergy_inner_identity
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (qi wo:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y) :
    let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    ∃wi wc:ℝ×SpherePolar.S→ℝ,Measurable wi ∧ Measurable wc ∧
      (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s Y.val) s wi) ∧
      (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s) s wc) ∧
      (toL2 g.leviCivitaData univ (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f):M→ℝ)
        =ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a (ball (0:E) 1))]
          coordinateExtension e (fun x:E=>F (a⁻¹ • x)+cylinderLift qi (a⁻¹ • x)+cylinderLift wi (a⁻¹ • x)) := by
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
  refine ⟨wi,wc,hwi,hwc,hi,ho,?_⟩
  let V:=e '' euclideanDilatedDomain a (ball (0:E) 1)
  have hV:IsOpen V:=e.isOpen_image_of_subset_source
    (isOpen_ball.preimage (continuous_const_smul a⁻¹)) ((nativeActualFeedback_inner_ball_fit W).trans hsource)
  filter_upwards [ae_restrict_of_ae (s:=V) (nativeOriginalSignedEnergyCLM_ae W T₀ Q₀ Rbase f),
    ae_restrict_of_ae (s:=V) hQb,ae_restrict_of_ae (s:=V) hQc,ae_restrict_mem hV.measurableSet] with y hz hb hc hy
  obtain ⟨x,hx,rfl⟩:=hy
  have hxK:=nativeActualFeedback_inner_ball_fit W hx
  have hxS:=hsource hxK
  rw [hz,hb,hc,nativeActualFeedback_core_one_inner W hx,sub_self,zero_mul,sub_zero]
  change nativeCompactChartFunction e (closedBall (0:E) R₀)
      (fun y:E=>χout (Real.exp S • (a⁻¹ • y))*u₀ (a⁻¹ • y)) (e x)+
    nativeCompactChartFunction e (closedBall (0:E) R₀)
      (fun y:E=>χout (Real.exp S • (a⁻¹ • y))*u₁ (a⁻¹ • y)) (e x)=_
  rw [nativeCompactChartFunction,coordinateExtension_comp_apply e _ hxS,indicator_of_mem hxK,
    nativeCompactChartFunction,coordinateExtension_comp_apply e _ hxS,indicator_of_mem hxK,
    coordinateExtension_comp_apply e _ hxS,nativeActualFeedback_outer_cutoff_one_inner W hx,one_mul,one_mul]
  simp only [u₀,u₁,piecewise_eq_of_mem _ _ _ (show a⁻¹ • x∈ball (0:E) 1 from hx)]

#print axioms nativeActualFeedback_inner_ball_fit
#print axioms nativeActualFeedback_core_one_inner
#print axioms nativeActualFeedback_outer_cutoff_one_inner
#print axioms nativeOriginalSignedEnergy_inner_identity
end Yamabe3.Analysis.SpherePolar
