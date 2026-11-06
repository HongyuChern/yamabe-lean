import Yamabe3.Analysis.NativeH2ExteriorCollarIdentification
import Yamabe3.Analysis.NativeBubbleExteriorL2Potential
import Yamabe3.Analysis.NativeOriginalCompensationEntranceZero
import Yamabe3.Analysis.NativeFiniteCompensationLocalZero
import Yamabe3.Analysis.NativeCompensationEntranceSupport
import Yamabe3.Analysis.NativeActualFeedbackCollarIdentity
import Yamabe3.Analysis.NativeOriginalWholeExteriorEquation
import Yamabe3.Analysis.NativeSmoothPotentialFixedFieldEquation
import Yamabe3.Analysis.NativeSmoothPotentialFeedback
import Yamabe3.Analysis.NativeOriginalWholeOuterWeakEquation
import Yamabe3.Analysis.NativeOriginalCompensationSource
import Yamabe3.Analysis.NativeWholeExteriorTestAdapter
import Yamabe3.Analysis.NativeWholeFullBubbleCompletedPairing
import Yamabe3.Analysis.NativeFullBubbleSignedPairing
import Yamabe3.Analysis.NativeL2ReactionSource

/-! The SAME original-source SIGNED completed field satisfies its
actual native weak equation on the whole native exterior. A fixed
computed compensation and the same full reaction construct one L2
source BEFORE all tests. This is the hard compact-chart full potential;
no smooth-paper truncation or conormal acceptance is inferred. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
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
theorem nativeSmoothExterior_same_collar_equation
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (χSm:E→ℝ) (hχone:∀x∈closedBall (0:E) 64,χSm x=1)
    (J K:nativeCollarJetClosure) (Z:H1Zero g.leviCivitaData univ)
    (C₀ C₁ F:Lp ℝ 2 g.volumeMeasure)
    (hC₀:(C₀:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)](fun _=>0))
    (hC₁:(C₁:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)](fun _=>0))
    (hFrep:(F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>(C₀+C₁:Lp ℝ 2 g.volumeMeasure) y+
      8*nativeScaledSmoothBubblePotential e τ a χSm y*toL2 g.leviCivitaData univ Z y))
    (hOuter:(Z,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' closedBall (0:E) a)ᶜ)
    (hrep:(toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict
      (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)]
      coordinateExtension e (fun x:E=>nativeCollarGluedFunction J.val.1 K.val.1 (a⁻¹ • x))):
    (nativeExteriorNativeJacobianCLM gE a (nativePoissonExteriorPotential (fullBubbleHighPotential (-τ))) K.val:E→ℝ)
      =ᵐ[volume.restrict nativeNegativeEntranceCollar](fun _=>0):=by
  let D:=euclideanDilatedDomain a nativeNegativeEntranceCollar
  let Dc:=euclideanDilatedDomain a nativePoissonEntranceCollar
  have hsub:D⊆Dc:=preimage_mono inter_subset_left
  have hD:IsOpen D:=nativeNegativeEntranceCollar_open.preimage (continuous_const_smul a⁻¹)
  have hDc:IsOpen Dc:=(nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹)
  have hfit:Dc⊆closedBall (0:E) R₀:=nativeActualFeedback_collar_fit W
  have hDK:closure D⊆closedBall (0:E) R₀:=closure_minimal (hsub.trans hfit) isClosed_closedBall
  have hDcomp:IsCompact (closure D):=(isCompact_closedBall (0:E) R₀).of_isClosed_subset isClosed_closure hDK
  have hDs:D⊆e.source:=(subset_closure.trans hDK).trans hsource
  have hΩ:IsOpen (e '' D):=e.isOpen_image_of_subset_source hD hDs
  have hΩc:IsOpen (e '' Dc):=e.isOpen_image_of_subset_source hDc (hfit.trans hsource)
  have haR:a≤R₀:=by nlinarith [W.receiving_fit]
  have hOut:e '' D⊆(e '' closedBall (0:E) a)ᶜ:=by
    rintro y ⟨x,hx,rfl⟩ ⟨z,hz,hez⟩
    have hzx:z=x:=e.injOn (hsource ((closedBall_subset_closedBall haR) hz)) (hDs hx) hez
    subst z
    have hn:‖a⁻¹ • x‖≤1:=by
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
      exact (inv_mul_le_one₀ ha).mpr (mem_closedBall_zero_iff.mp hz)
    exact (not_le_of_gt hx.2) hn
  have hrepK:(toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' D)]
      coordinateExtension e (fun x:E=>(K.val.1:E→ℝ) (a⁻¹ • x)):=by
    filter_upwards [ae_mono (Measure.restrict_mono (image_mono hsub) le_rfl) hrep,
      ae_restrict_mem hΩ.measurableSet] with y hy hyD
    obtain ⟨x,hx,rfl⟩:=hyD
    rw [hy,coordinateExtension_comp_apply e _ (hDs hx),coordinateExtension_comp_apply e _ (hDs hx)]
    exact piecewise_eq_of_notMem _ _ _ (by simpa only [mem_ball_zero_iff] using (not_lt_of_ge hx.2.le))
  have hval:(F:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' D)]
      (fun y=>8*nativeScaledSmoothBubblePotential e τ a χSm y*toL2 g.leviCivitaData univ Z y):=by
    have hμ: g.volumeMeasure.restrict (e '' D)≤g.volumeMeasure.restrict (e '' Dc):=
      Measure.restrict_mono (image_mono hsub) le_rfl
    filter_upwards [ae_mono hμ hC₀,ae_mono hμ hC₁,ae_restrict_of_ae (s:=e '' D) hFrep,
      ae_restrict_of_ae (s:=e '' D) (Lp.coeFn_add C₀ C₁)] with y h₀ h₁ hf hadd
    rw [hf,hadd]
    change C₀ y+C₁ y+_= _
    rw [h₀,h₁,add_zero,zero_add]
  have hp:=nativeRestrictedChart_ae_pullback g e he hei (isCompact_closedBall (0:E) R₀) hsource
    hD.measurableSet (hsub.trans hfit) hΩ.measurableSet subset_rfl hval
  have hr:=nativeRestrictedChart_ae_pullback g e he hei (isCompact_closedBall (0:E) R₀) hsource
    hD.measurableSet (hsub.trans hfit) hΩ.measurableSet subset_rfl hrepK
  have hp':=ae_comp_dilation ha.ne' hp
  have hr':=ae_comp_dilation ha.ne' hr
  simp only [D,euclideanDilatedDomain,preimage_preimage,Function.comp_def,smul_smul,
    inv_mul_cancel₀ ha.ne',one_smul] at hp' hr'
  apply nativeH2_exterior_collar_identification g gE e he hei (isCompact_closedBall (0:E) R₀)
    hsource hcoeff ha hDcomp hDK _ K Z F hrepK
    (fun φ hs=>hOuter φ (hs.trans hOut))
  filter_upwards [hp',hr',ae_restrict_mem nativeNegativeEntranceCollar_open.measurableSet] with x hf hr hx
  have hxa:a • x∈e.source:=hDs (by
    change a⁻¹ • (a • x)∈nativeNegativeEntranceCollar
    simpa only [smul_smul,inv_mul_cancel₀ ha.ne',one_smul] using hx)
  have hx0:x≠0:=hx.1.1
  have hx64:x∈closedBall (0:E) 64:=mem_closedBall_zero_iff.mpr
    ((nativeEntranceCollar_closure_subset_basic (subset_closure hx.1)).2.le.trans (by norm_num))
  rw [hf,hr,coordinateExtension_comp_apply e _ hxa]
  simp only [nativeScaledSmoothBubblePotential,coordinateExtension_comp_apply e _ hxa,
    smul_smul,inv_mul_cancel₀ ha.ne',one_smul,hχone x hx64,one_mul]
  rw [nativeBubbleExteriorPotential_eq_phase,
    nativeHalfEnd_fullBubble_spatial_eq τ hx0]
  ring

#print axioms nativeSmoothExterior_same_collar_equation
end Yamabe3.Analysis.SpherePolar
