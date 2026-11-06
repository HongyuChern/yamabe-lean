import Yamabe3.Analysis.NativeActualNegativeFeedbackSourceCutoff
import Yamabe3.Analysis.NativeTwoSidedNativeEnergy
import Yamabe3.Analysis.NativeFeedbackCorrectedEnergy
import Yamabe3.Analysis.NativeScaledCutoffGeometry

/-! A jointly produced actual source feedback and SAME completed
physical field. The record alone asserts no existence: the theorem
below constructs every component from the actual producers. The full
native PDE/conormal cancellation remains a separate explicit gate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def actualBundleH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] actualBundleH1Normed

variable (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
  (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (R₀:ℝ) (hsource:closedBall (0:E) R₀⊆e.source)
  (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1)
  (τ cTail:ℝ) (ht:0 < τ) (m n:ℕ) (b S CR CM:ℝ)
  (χin χout:E→ℝ) (hχin:ContDiff ℝ ∞ χin) (hχout:ContDiff ℝ ∞ χout)

structure NativeActualFeedbackEnergyBundle (a:ℝ) (ha:0 < a) (ha1:a ≤ 1) where
  open_domain:IsOpen (e '' ball (0:E) (a*64))
  inner_plateau:∀x∈closedBall (0:E) 2,χin=ᶠ[𝓝 x](fun _=>1)
  inner_compact:HasCompactSupport χin
  inner_support:tsupport χin⊆ball (0:E) 3
  inner_range:∀x:E,0 ≤ χin x ∧ χin x ≤ 1
  outer_plateau:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χout=ᶠ[𝓝 x](fun _=>1)
  outer_support:tsupport χout⊆ball (0:E) (Real.exp (1/8:ℝ))
  outer_compact:HasCompactSupport χout
  outer_derivatives:∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
    partialDeriv i χout x=0 ∧ partialDeriv i (partialDeriv i χout) x=0
  near_support:b ≤ -(m:ℝ)/2-1
  tail_window:cTail < (m:ℝ)/2
  far_window:-S+1/2 < ((m+n:ℕ):ℝ)/2
  far_scale:S ≤ -1
  source_cutoff:S ≤ b-1
  receiving_fit:a*64 ≤ R₀
  J:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)) →L[ℝ] RegularLowH4Space
  U:H1Zero g.leviCivitaData univ →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ)
  I:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)) →L[ℝ] nativeSupportedSourcePairSpace b
  R:nativeSupportedSourcePairSpace b →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))
  T:nativeSupportedSourcePairSpace b →L[ℝ] nativeSupportedSourcePairSpace b
  feedback_bound:‖T‖ ≤ 4
  return_bound:‖R‖ ≤ CR*Real.sqrt a
  incoming:NativeIncomingSourceRealization g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))
    open_domain gE e a τ cTail χin hχin (ball (0:E) (Real.exp cTail+1)) b J U I
  far:NativeFarTailRealization g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)) gE e
    (closedBall (0:E) R₀) P hp v hv hb b ht a S cTail n
    (fun i:Fin n=>nativeOuterLogShellCenter (m+i.val)) χout hχout R
  source_fixed:∀X,(T X).val=X.val+nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (T X).val+
    -(I (R (T X))).val
  inner_source_fixed:∀X,(T X).val.1=X.val.1+nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a (T X).val
  LE:NativeTwoSidedSource →L[ℝ] H1Zero Deuc (ball (0:E) (Real.exp ((1/8:ℝ)-S)+1))
  model_field:∀Y:NativeTwoSidedSource,∃wi wo:ℝ×SpherePolar.S→ℝ,Measurable wi ∧ Measurable wo ∧
    (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s Y) s wi) ∧
    (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y s) s wo) ∧
    (toL2 Deuc (ball (0:E) (Real.exp ((1/8:ℝ)-S)+1)) (LE Y):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wo) y
  Q:NativeTwoSidedSource →L[ℝ] H1Zero g.leviCivitaData univ
  native_field_bound:‖Q‖ ≤ CM*Real.sqrt a
  native_field_class:∀Y:NativeTwoSidedSource,toL2 g.leviCivitaData univ (Q Y)=
    nativeCompactChartL2CLM g e he hei (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 Deuc (ball (0:E) (Real.exp ((1/8:ℝ)-S)+1)) (LE Y)))
  core:EnergyTest g.leviCivitaData univ
  core_coordinate:(core:M→ℝ)=coordinateExtension e (fun x:E=>χin (a⁻¹ • x))
  core_value:∀x:E,a • x∈e.source → core (e (a • x))=χin x
  Z:nativeSupportedSourcePairSpace b →L[ℝ] H1Zero g.leviCivitaData univ
  corrected_field:Z=nativeNegativeFeedbackEnergyCLM g core core.smooth
    (Q.comp (nativeSupportedSourcePairSpace b).subtypeL) T
    ((nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))).subtypeL.comp R)
  corrected_class:∀X:nativeSupportedSourcePairSpace b,
    (toL2 g.leviCivitaData univ (Z X):M→ℝ)=ᵐ[g.volumeMeasure]
      fun y=>toL2 g.leviCivitaData univ (Q (T X).val) y-
        (1-core y)*toL2 g.leviCivitaData univ (R (T X)).val y

theorem exists_nativeActual_completed_negative_feedback
    (hY:0 < Target.yamabeConstant g) (hR₀:0 < R₀)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1) :
    ∃(cTail:ℝ) (m n:ℕ) (b S δ CR CM:ℝ) (χin χout:E→ℝ)
      (hχin:ContDiff ℝ ∞ χin) (hχout:ContDiff ℝ ∞ χout),
      0 < δ ∧ 0 ≤ CR ∧ 0 ≤ CM ∧ ∀a:ℝ,∀ha:0 < a,a ≤ δ → ∃ha1:a ≤ 1,
        Nonempty (NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
          (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
          (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
          (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1) := by
  obtain ⟨cTail,m,n,b,S,δ₀,CR,χin,χout,hχin,hχout,hCR,hχinc,hχins,hχrange,hχoutc,hχoutd,
      hδ₀,hmTail,hbm,hSm,hSb,hMcover,hχin1,hχout1,hχouts,hroot⟩:=
    exists_nativeActual_negative_source_feedback_source_cutoff g hY gE e he hei hR₀ hsource hcoeff hB hρ P hp v hv hb ht
  let H:=Real.exp ((1/8:ℝ)-S)+1
  have hH:0 < H:=by dsimp only [H];positivity
  let O:=ball (0:E) H
  have hO:tsupport (fun y:E=>χout (Real.exp S • y))⊆O := by
    apply (nativeScaledCutoff_support hχouts S).trans
    apply ball_subset_ball
    dsimp only [H]
    rw [←Real.exp_add]
    simpa only [sub_eq_add_neg] using (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num):
      Real.exp ((1/8:ℝ)+(-S)) ≤ Real.exp ((1/8:ℝ)+(-S))+1)
  obtain ⟨LE,CM,hCM,hLE,hLift⟩:=exists_nativeTwoSided_native_cutoff_energy_family g e he hei
    (isCompact_closedBall (0:E) R₀) hsource P hp v hv hb b ht χout hχout hχoutc hχouts hχout1 S O hO
  let δ:=min δ₀ (min (1/2:ℝ) (min (R₀/128) (R₀/(2*H))))
  have hδ:0 < δ:=by dsimp only [δ];positivity
  refine ⟨cTail,m,n,b,S,δ,CR,CM,χin,χout,hχin,hχout,hδ,hCR,hCM,fun a ha had=>?_⟩
  have had₀:a ≤ δ₀:=had.trans (min_le_left _ _)
  have haHalf:a ≤ 1/2:=had.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1:a ≤ 1:=haHalf.trans (by norm_num)
  have ha128:a ≤ R₀/128:=had.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haH:a ≤ R₀/(2*H):=had.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h128:a*128 ≤ R₀:=(le_div_iff₀ (by norm_num:(0:ℝ) < 128)).mp ha128
  have h64:a*64 ≤ R₀:=by linarith
  have h4:a*4 ≤ R₀:=by linarith
  have hsrc64:ball (0:E) (a*64)⊆e.source:=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall h64).trans hsource)
  have hΩ:IsOpen (e '' ball (0:E) (a*64)):=e.isOpen_image_of_subset_source isOpen_ball hsrc64
  have hsmall:60*(∫x,|(0:ℝ)|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g:=by simpa using hY.le
  obtain ⟨A,J,U,I,R,T,hA,hT,hRb,hAv,hInc,hFar,hFix⟩:=
    hroot a ha had₀ (fun _:M=>0) contMDiff_const hsmall hΩ (fun _ _=>rfl)
  have haHr:a*H ≤ R₀:=by
    have hh: a*(2*H) ≤ R₀:=(le_div_iff₀ (by positivity:0 < 2*H)).mp haH
    nlinarith [mul_nonneg ha.le hH.le]
  have hfit:euclideanDilatedDomain a O⊆closedBall (0:E) R₀:=euclideanDilatedBall_subset_closedBall ha haHr
  obtain ⟨Q,hQ,hQv⟩:=hLift a ha ha1 hfit
  have hcorefit:euclideanDilatedDomain a (ball (0:E) 4)⊆e.source:=
    (euclideanDilatedBall_subset_closedBall ha h4).trans hsource
  let core:=nativeChartScaledCutoffTest g e hei ha χin hχin hχinc (ball (0:E) 4)
    (hχins.trans (ball_subset_ball (by norm_num:(3:ℝ) ≤ 4))) hcorefit
  let LL:=Q.comp (nativeSupportedSourcePairSpace b).subtypeL
  let RR:=(nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))).subtypeL.comp R
  let Z:=nativeNegativeFeedbackEnergyCLM g core core.smooth LL T RR
  refine ⟨ha1,⟨{
    open_domain:=hΩ
    inner_plateau:=hχin1
    inner_compact:=hχinc
    inner_support:=hχins
    inner_range:=hχrange
    outer_plateau:=hχout1
    outer_support:=hχouts
    outer_compact:=hχoutc
    outer_derivatives:=hχoutd
    near_support:=hbm
    tail_window:=hmTail
    far_window:=hMcover
    far_scale:=hSm.trans (by have hm:0 ≤ (m:ℝ):=Nat.cast_nonneg _;linarith)
    source_cutoff:=hSb
    receiving_fit:=h64
    J:=J
    U:=U
    I:=I
    R:=R
    T:=T
    feedback_bound:=hT
    return_bound:=hRb
    incoming:=hInc
    far:=hFar
    source_fixed:=hFix
    inner_source_fixed:=?_
    LE:=LE
    model_field:=hLE
    Q:=Q
    native_field_bound:=hQ
    native_field_class:=hQv
    core:=core
    core_coordinate:=rfl
    core_value:=?_
    Z:=Z
    corrected_field:=rfl
    corrected_class:=?_}⟩⟩
  · intro X
    have hi0:((I (R (T X))).val).1=0:=by rw [hInc.2.1]
    have hh:=congrArg Prod.fst (hFix X)
    change (T X).val.1=X.val.1+nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a (T X).val+
      -((I (R (T X))).val).1 at hh
    simpa only [hi0,neg_zero,add_zero] using hh
  · intro x hx
    exact nativeChartScaledCutoffTest_apply g e hei ha χin hχin hχinc (ball (0:E) 4)
      (hχins.trans (ball_subset_ball (by norm_num:(3:ℝ) ≤ 4))) hcorefit x hx
  · intro X
    exact nativeNegativeFeedbackEnergyCLM_ae g core core.smooth LL T RR X

#print axioms exists_nativeActual_completed_negative_feedback
end Yamabe3.Analysis.SpherePolar
