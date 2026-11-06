import Yamabe3.Analysis.NativeSupportedGeometricSource
import Yamabe3.Analysis.NativeTwoSidedGlobalFeedback
import Yamabe3.Analysis.NativeFullCollarSourceSupport

/-! A newly constructed bounded feedback inverse for the supported outer
producer, retaining the actual inner global operator. The same fixed point
preserves outer lower support and reconstructs its physical source. -/
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
  (b : ℝ) {t₀ : ℝ} (ht : 0<t₀)

theorem exists_nativeSupportedTwoSidedGlobal_feedback
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ε : ℝ,0≤ε → ε≤ε₀ → ∀a∈Λ,
      ∃T : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource,‖T‖≤2 ∧ ∀X,
        T X=X+nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht (g a) ε (T X) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeSupportedTwoSidedGlobalSource_bound P hp v hv hb b ht Λ g hB hρ
  refine ⟨min 1 (1/(2*C)),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro ε hε hε0 a ha
  have hK : ‖nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht (g a) ε‖≤1/2 := by
    apply (hc ε hε (hε0.trans (min_le_left _ _)) a ha).trans
    have he := mul_le_mul_of_nonneg_left (hε0.trans (min_le_right _ _)) hC.le
    exact he.trans_eq (by field_simp)
  let K := nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht (g a) ε
  exact ⟨nativeTwoSidedFeedbackCLM K hK,nativeTwoSidedFeedback_norm K hK,nativeTwoSidedFeedback_fixed K hK⟩

theorem nativeSupportedTwoSidedGlobal_fixed_pairing
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (X Y : NativeTwoSidedSource) (hY : Y=X+nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht (g a) ε Y)
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

theorem nativeSupportedTwoSidedGlobal_outer_source_identity (g : RiemannianMetric 3 E) (ε : ℝ)
    (X Y : NativeTwoSidedSource) (hY : Y=X+nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht g ε Y) :
    nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM X.2+
      nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g ε Y := by
  have h := congrArg (fun Z : NativeTwoSidedSource => nativeL2FullPhysicalSourceCLM Z.2) hY
  change nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM
    (X.2+nativeFullCollarSourceReturnCLM (nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g ε Y)) at h
  rwa [map_add,nativeFullCollarSourceReturn_right_inverse] at h


variable (g : RiemannianMetric 3 E) (ε : ℝ) (X Y : NativeTwoSidedSource)
  (hY : Y=X+nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht g ε Y)

include hY in
theorem nativeSupportedTwoSidedGlobal_outer_source_off_collar :
    ∀ᵐt : ℝ ∂volume,t∉Icc (-(1/2:ℝ)) (1/2) → Y.2 t=X.2 t := by
  have hy := congrArg (fun Z : NativeTwoSidedSource => Z.2) hY
  change Y.2=X.2+nativeFullCollarSourceReturnCLM (nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g ε Y) at hy
  rw [hy]
  filter_upwards [Lp.coeFn_add X.2 (nativeFullCollarSourceReturnCLM (nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g ε Y)),
    nativeFullCollarSourceReturn_time_support (nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g ε Y)] with t ha hz
  intro hc
  rw [ha]
  change X.2 t+nativeFullCollarSourceReturnCLM (nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g ε Y) t=X.2 t
  rw [hz hc,add_zero]

include hY in
theorem nativeSupportedTwoSidedGlobal_outer_source_lower_support (hb0 : b≤ -(1/2:ℝ))
    (hX : ∀ᵐt : ℝ ∂volume,t<b → X.2 t=0) :
    ∀ᵐt : ℝ ∂volume,t<b → Y.2 t=0 := by
  filter_upwards [nativeSupportedTwoSidedGlobal_outer_source_off_collar P hp v hv hb b ht g ε X Y hY,hX] with t hy hx
  intro htb
  have hc : t∉Icc (-(1/2:ℝ)) (1/2) := by intro h;linarith [h.1]
  exact (hy hc).trans (hx htb)


#print axioms exists_nativeSupportedTwoSidedGlobal_feedback
#print axioms nativeSupportedTwoSidedGlobal_fixed_pairing
#print axioms nativeSupportedTwoSidedGlobal_outer_source_identity
#print axioms nativeSupportedTwoSidedGlobal_outer_source_off_collar
#print axioms nativeSupportedTwoSidedGlobal_outer_source_lower_support
end Yamabe3.Analysis.SpherePolar
