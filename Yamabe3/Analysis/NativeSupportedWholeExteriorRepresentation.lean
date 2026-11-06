import Yamabe3.Analysis.NativeAllScaleFieldUniqueness
import Yamabe3.Analysis.NativeOriginalSignedOuterGlobalClass
import Yamabe3.Analysis.NativeOuterClassWindowExtension

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

 theorem nativeSupported_completed_whole_exterior_representation
    (Y:nativeSupportedSourcePairSpace b) (w:ℝ×SpherePolar.S→ℝ)
    (hw:∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s) s w)
    (vaux:E→ℝ)
    (hAux:EqOn vaux (fun y=>χout (Real.exp S • y)*cylinderLift w y)
      (nativePolarTimeWindow (Ioc (-((m+n:ℕ):ℝ)/2) 0)))
    (hzero:∀y:E,χout (Real.exp S • y)=0→vaux y=0)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀):
    (toL2 g.leviCivitaData univ (W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' closedBall (0:E) a)ᶜ]
      coordinateExtension e (fun y:E=>vaux (a⁻¹ • y)):=by
  obtain ⟨wi,wc,hwi,hwc,hij,hco,hE⟩:=W.model_field Y.val
  have hsum:cylinderLift wc=ᵐ[volume]cylinderLift w:=native_all_scale_jet_same_volume_class
    (fun s=>nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val s) hco hw
  let u₀:E→ℝ:=(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wc)
  let u:E→ℝ:=(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift w)
  have hu:u₀=ᵐ[volume]u:=by
    filter_upwards [hsum] with x hx
    by_cases hxB:x∈ball (0:E) 1
    · simp only [u₀,u,piecewise_eq_of_mem _ _ _ hxB]
    · simpa only [u₀,u,piecewise_eq_of_notMem _ _ _ hxB] using hx
  have hud:=ae_comp_dilation (inv_ne_zero ha.ne') (ae_restrict_of_ae (s:=univ) hu)
  simp only [preimage_univ,Measure.restrict_univ] at hud
  have hcoord:(fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u₀ (a⁻¹ • x))=ᵐ[volume]
      (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u (a⁻¹ • x)):=by
    filter_upwards [hud] with x hx
    exact congrArg (fun z:ℝ=>χout (Real.exp S • (a⁻¹ • x))*z) hx
  have hnat:=nativeCompactChart_congr_volume_ae g e he hei (isCompact_closedBall (0:E) R₀).measurableSet
    (ae_restrict_of_ae (s:=closedBall (0:E) R₀) hcoord)
  have hQc:(toL2 g.leviCivitaData univ (W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u₀ (a⁻¹ • x)):=by
    rw [W.native_field_class]
    exact nativeCompletedChartL2_same_function g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
      (W.LE Y.val) (fun y=>χout (Real.exp S • y)*u₀ y) hE
  have hQ:(toL2 g.leviCivitaData univ (W.Q Y.val):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u (a⁻¹ • x)):=hQc.trans hnat
  have hAuxGlobal:=nativeOuterCutoff_window_class_extends W.outer_support W.far_window hAux hzero
  have hOffK:=nativeOuterCutoff_realization_zero_off_chart ha W.outer_support W.far_window hzero hfit
  have hsmall:a≤R₀:=by nlinarith only [W.receiving_fit,ha]
  have hBallS:closedBall (0:E) a⊆e.source:=(closedBall_subset_closedBall hsmall).trans hsource
  have hImg:IsCompact (e '' closedBall (0:E) a):=(isCompact_closedBall (0:E) a).image_of_continuousOn
    (e.continuousOn.mono hBallS)
  have hΩ:IsOpen (e '' closedBall (0:E) a)ᶜ:=hImg.isClosed.isOpen_compl
  filter_upwards [ae_restrict_of_ae (s:=(e '' closedBall (0:E) a)ᶜ) hQ,
    ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
  rw [hy]
  by_cases hyT:y∈e.target
  · rw [nativeCompactChartFunction,coordinateExtension_apply e _ hyT,coordinateExtension_apply e _ hyT]
    have hxBall:e.symm y∉closedBall (0:E) a:=by
      intro hx
      exact hyΩ ⟨e.symm y,hx,e.right_inv hyT⟩
    have hn:a<‖e.symm y‖:=by
      by_contra! hh
      exact hxBall (mem_closedBall_zero_iff.mpr hh)
    have hnorm:a*‖a⁻¹ • e.symm y‖=‖e.symm y‖:=by
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
    have hu:1<‖a⁻¹ • e.symm y‖:=by nlinarith only [ha,hn,hnorm]
    have hxB:a⁻¹ • e.symm y∉ball (0:E) 1:=fun hx=>not_lt_of_ge hu.le (mem_ball_zero_iff.mp hx)
    by_cases hxK:e.symm y∈closedBall (0:E) R₀
    · rw [indicator_of_mem hxK]
      dsimp only [u]
      rw [piecewise_eq_of_notMem _ _ _ hxB]
      exact (hAuxGlobal hu).symm
    · rw [indicator_of_notMem hxK]
      exact (hOffK (e.symm y) hxK).symm
  · simp only [nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hyT]

#print axioms nativeSupported_completed_whole_exterior_representation
end Yamabe3.Analysis.SpherePolar
