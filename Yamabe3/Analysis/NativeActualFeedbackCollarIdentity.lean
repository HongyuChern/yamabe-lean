import Yamabe3.Analysis.NativeActualFeedbackEnergyBundle
import Yamabe3.Analysis.NativeCompletedChartSameFunction
import Yamabe3.Analysis.NativeH4CollarRealization

/-! The actual signed completed field has the SAME model representative
on the full physical interface collar. All identities are in volume;
none is restricted to a sphere. This is the locality bridge for the
subsequent actual boundary trace/Green identification. -/
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
theorem nativeActualFeedback_collar_fit :
    euclideanDilatedDomain a nativePoissonEntranceCollar⊆closedBall (0:E) R₀ := by
  have h4:a*4 ≤ R₀:=by nlinarith [W.receiving_fit]
  intro x hx
  apply euclideanDilatedBall_subset_closedBall ha h4
  apply mem_ball_zero_iff.mpr
  have hh:‖a⁻¹ • x‖ < 2:=(nativeEntranceCollar_closure_subset_basic (subset_closure hx)).2
  linarith

include W in
theorem nativeActualFeedback_outer_cutoff_one {x:E} (hx:x∈nativePoissonEntranceCollar) :
    χout (Real.exp S • x)=1 := by
  have hn:‖x‖ < Real.exp (1/2:ℝ):=((nativePolarTimeWindow_norm (1/2) x).mp hx).2
  have hh:‖Real.exp S • x‖ ≤ Real.exp (-(1/8:ℝ)) := by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    apply (mul_lt_mul_of_pos_left hn (Real.exp_pos S)).le.trans
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [W.far_scale])
  exact (W.outer_plateau _ (by simpa only [mem_closedBall,dist_zero_right] using hh)).self_of_nhds

theorem nativeActualFeedback_core_one {x:E}
    (hx:x∈euclideanDilatedDomain a nativePoissonEntranceCollar) : W.core (e x)=1 := by
  have hxK:=nativeActualFeedback_collar_fit W hx
  have hxS:=hsource hxK
  have hh: a • (a⁻¹ • x)=x:=by rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have hv:=W.core_value (a⁻¹ • x) (by simpa only [hh] using hxS)
  rw [hh] at hv
  have hn:‖a⁻¹ • x‖ < 2:=(nativeEntranceCollar_closure_subset_basic (subset_closure hx)).2
  exact hv.trans ((W.inner_plateau _ (by simpa only [mem_closedBall,dist_zero_right] using hn.le)).self_of_nhds)

theorem nativeActualFeedback_completed_collar_identity (X:nativeSupportedSourcePairSpace b) :
    ∃wi wo:ℝ×SpherePolar.S→ℝ,Measurable wi ∧ Measurable wo ∧
      (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s (W.T X).val) s wi) ∧
      (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (W.T X).val s) s wo) ∧
      (toL2 g.leviCivitaData univ (W.Z X):M→ℝ)=ᵐ[g.volumeMeasure.restrict
        (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)]
        coordinateExtension e (fun x:E=>(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wo) (a⁻¹ • x)) := by
  obtain ⟨wi,wo,hwi,hwo,hi,ho,hE⟩:=W.model_field (W.T X).val
  let u:E→ℝ:=(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wo)
  have hQ:(toL2 g.leviCivitaData univ (W.Q (W.T X).val):M→ℝ)=ᵐ[g.volumeMeasure]
      nativeCompactChartFunction e (closedBall (0:E) R₀) (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u (a⁻¹ • x)) := by
    rw [W.native_field_class]
    exact nativeCompletedChartL2_same_function g e he hei (isCompact_closedBall (0:E) R₀) hsource ha ha1
      (W.LE (W.T X).val) (fun y:E=>χout (Real.exp S • y)*u y) hE
  let V:=e '' euclideanDilatedDomain a nativePoissonEntranceCollar
  have hVs:euclideanDilatedDomain a nativePoissonEntranceCollar⊆e.source:=
    (nativeActualFeedback_collar_fit W).trans hsource
  have hV:IsOpen V:=e.isOpen_image_of_subset_source
    ((nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹)) hVs
  refine ⟨wi,wo,hwi,hwo,hi,ho,?_⟩
  filter_upwards [ae_restrict_of_ae (s:=V) (W.corrected_class X),ae_restrict_of_ae (s:=V) hQ,
    ae_restrict_mem hV.measurableSet] with y hz hq hy
  obtain ⟨x,hx,rfl⟩:=hy
  have hxK:=nativeActualFeedback_collar_fit W hx
  have hxS:=hsource hxK
  rw [hz,hq,nativeActualFeedback_core_one W hx,sub_self,zero_mul,sub_zero]
  change nativeCompactChartFunction e (closedBall (0:E) R₀)
    (fun x:E=>χout (Real.exp S • (a⁻¹ • x))*u (a⁻¹ • x)) (e x)=
      coordinateExtension e (fun x:E=>u (a⁻¹ • x)) (e x)
  rw [nativeCompactChartFunction,coordinateExtension_comp_apply e _ hxS,indicator_of_mem hxK,
    coordinateExtension_comp_apply e _ hxS,nativeActualFeedback_outer_cutoff_one W hx,one_mul]

#print axioms nativeActualFeedback_collar_fit
#print axioms nativeActualFeedback_outer_cutoff_one
#print axioms nativeActualFeedback_core_one
#print axioms nativeActualFeedback_completed_collar_identity
end Yamabe3.Analysis.SpherePolar
