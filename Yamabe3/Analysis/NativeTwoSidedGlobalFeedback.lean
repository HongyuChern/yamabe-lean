import Yamabe3.Analysis.NativeTwoSidedGlobalJacobian
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! Actual global inner/outer-collar feedback on one source pair. The
same pair is used for all half-end scales and the actual matching traces.
The inner source pairing and the outer physical source identity are
proved from the same fixed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
  {t₀ : ℝ} (ht : 0<t₀)

theorem exists_nativeTwoSidedGlobal_feedback
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ε : ℝ,0≤ε → ε≤ε₀ → ∀a∈Λ,
      ∃T : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource,‖T‖≤2 ∧ ∀X,
        T X=X+nativeTwoSidedGlobalSourceCLM P hp v hv hb ht (g a) ε (T X) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedGlobalSource_bound P hp v hv hb ht Λ g hB hρ
  refine ⟨min 1 (1/(2*C)),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro ε hε hε0 a ha
  have hK : ‖nativeTwoSidedGlobalSourceCLM P hp v hv hb ht (g a) ε‖≤1/2 := by
    apply (hc ε hε (hε0.trans (min_le_left _ _)) a ha).trans
    have he := mul_le_mul_of_nonneg_left (hε0.trans (min_le_right _ _)) hC.le
    exact he.trans_eq (by field_simp)
  let K := nativeTwoSidedGlobalSourceCLM P hp v hv hb ht (g a) ε
  exact ⟨nativeTwoSidedFeedbackCLM K hK,nativeTwoSidedFeedback_norm K hK,nativeTwoSidedFeedback_fixed K hK⟩

theorem nativeTwoSidedGlobal_fixed_pairing
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (X Y : NativeTwoSidedSource) (hY : Y=X+nativeTwoSidedGlobalSourceCLM P hp v hv hb ht (g a) ε Y)
    (G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (hG0 : ∀ᵐt : ℝ ∂volume,t≤0 → G t=0) :
    HasSum (fun n => inner ℝ (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ (g a) ε (nativeLogShellCenter n) Y)) G)
      (-inner ℝ X.1 G) := by
  have hs := nativeTwoSidedJacobian_pairing P hp v hv hb t₀ hpot Λ g hB hρ ε hε hε1 a ha Y G
  rw [←nativeFullPositiveTest_pairing Y.1 G hG0] at hs
  have hi := congrArg (fun Z : NativeTwoSidedSource => inner ℝ Z.1 G) hY
  change inner ℝ Y.1 G=inner ℝ (X.1+nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε Y) G at hi
  rw [inner_add_left] at hi
  have he : -inner ℝ Y.1 G+inner ℝ (nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε Y) G= -inner ℝ X.1 G := by
    linarith only [hi]
  rwa [he] at hs

theorem nativeTwoSidedGlobal_outer_source_identity (g : RiemannianMetric 3 E) (ε : ℝ)
    (X Y : NativeTwoSidedSource) (hY : Y=X+nativeTwoSidedGlobalSourceCLM P hp v hv hb ht g ε Y) :
    nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM X.2+
      nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g ε Y := by
  have h := congrArg (fun Z : NativeTwoSidedSource => nativeL2FullPhysicalSourceCLM Z.2) hY
  change nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM
    (X.2+nativeFullCollarSourceReturnCLM (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g ε Y)) at h
  rwa [map_add,nativeFullCollarSourceReturn_right_inverse] at h

theorem nativeTwoSidedGlobal_same_field_matching (Y : NativeTwoSidedSource) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      (∀s : ℝ,((nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s Y).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x)) ∧
        MemWkp 2 2 (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s Y).1 nativePoissonEntranceCollar) ∧
      NativeCollarWeakGluing (nativeTwoSidedAllScaleJetCLM P hp v hv hb t₀ 0 Y)
        (nativeTwoSidedExteriorJetCLM P hp v hv hb ht Y) := by
  obtain ⟨w,hw,hjet⟩ := nativeTwoSidedAllScale_same_field P hp v hv hb t₀ Y
  have hm (s : ℝ) := nativeTwoSidedAllScale_memH2 P hp v hv hb t₀ s Y
  have hlocal : MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) :=
    native_all_scale_H2_local (fun s =>
      (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hjet s)).mp (hm s))
  exact ⟨w,hw,hlocal,fun s => ⟨hjet s,hm s⟩,nativeTwoSidedSource_actual_weak_gluing P hp v hv hb ht Y⟩

#print axioms exists_nativeTwoSidedGlobal_feedback
#print axioms nativeTwoSidedGlobal_fixed_pairing
#print axioms nativeTwoSidedGlobal_outer_source_identity
#print axioms nativeTwoSidedGlobal_same_field_matching
end Yamabe3.Analysis.SpherePolar
