import Yamabe3.Analysis.NativeTwoSidedCollarGeometricSource
import Yamabe3.Analysis.SmallErrorBoundedSolver

/-! Solve the actual two-sided collar source feedback, preserving its
physical reconstruction and one common matched pair. The radius here is
chosen after the fixed model and entrance time, before metric index and
sources. Global original-source/end estimates remain separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

private theorem feedback_small (K : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource)
    (hK : ‖K‖≤1/2) : ‖ContinuousLinearMap.id ℝ NativeTwoSidedSource‖*‖-K‖≤1/2 := by
  rw [norm_neg]
  exact (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg K)).trans
    (by simpa only [one_mul] using hK)

def nativeTwoSidedFeedbackCLM (K : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource)
    (hK : ‖K‖≤1/2) : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource :=
  smallErrorSolutionCLM (ContinuousLinearMap.id ℝ _) (-K) (feedback_small K hK)

theorem nativeTwoSidedFeedback_fixed (K : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource)
    (hK : ‖K‖≤1/2) (X : NativeTwoSidedSource) :
    nativeTwoSidedFeedbackCLM K hK X=X+K (nativeTwoSidedFeedbackCLM K hK X) := by
  exact (smallErrorSolution_fixed (ContinuousLinearMap.id ℝ _) (-K)
    (feedback_small K hK) X).symm.trans (by simp only
      [ContinuousLinearMap.id_apply,ContinuousLinearMap.neg_apply,sub_neg_eq_add];rfl)

theorem nativeTwoSidedFeedback_norm (K : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource)
    (hK : ‖K‖≤1/2) : ‖nativeTwoSidedFeedbackCLM K hK‖≤2 :=
  (smallErrorSolutionCLM_norm _ _ _).trans (by
    nlinarith [ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=NativeTwoSidedSource)])

theorem nativeTwoSidedFeedback_unique (K : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource)
    (hK : ‖K‖≤1/2) (X Y : NativeTwoSidedSource) (hY : Y=X+K Y) :
    Y=nativeTwoSidedFeedbackCLM K hK X := by
  symm
  apply smallErrorSolution_unique (ContinuousLinearMap.id ℝ _) (-K) (feedback_small K hK) X Y
  simpa only [ContinuousLinearMap.id_apply,ContinuousLinearMap.neg_apply,sub_neg_eq_add] using hY.symm

variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
  {t₀ : ℝ} (ht : 0<t₀)

theorem nativeTwoSidedCollarFeedback_physical_identity (g : RiemannianMetric 3 E) (r : ℝ)
    (hK : ‖nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r‖≤1/2) (X : NativeTwoSidedSource) :
    let Y := nativeTwoSidedFeedbackCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r) hK X
    nativeL2FullPhysicalSourceCLM Y.1=nativeL2FullPhysicalSourceCLM X.1+
      nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) g r Y ∧
    nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM X.2+
      nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g r Y := by
  dsimp only
  let K := nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r
  let Y := nativeTwoSidedFeedbackCLM K hK X
  have he : Y=X+K Y := nativeTwoSidedFeedback_fixed K hK X
  have hi := congrArg (fun Z : NativeTwoSidedSource => nativeL2FullPhysicalSourceCLM Z.1) he
  have ho := congrArg (fun Z : NativeTwoSidedSource => nativeL2FullPhysicalSourceCLM Z.2) he
  change nativeL2FullPhysicalSourceCLM Y.1=nativeL2FullPhysicalSourceCLM (X.1+(K Y).1) at hi
  change nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM (X.2+(K Y).2) at ho
  rw [map_add,(nativeTwoSidedCollarSourceError_reconstructs P hp v hv hb ht g r Y).1] at hi
  rw [map_add,(nativeTwoSidedCollarSourceError_reconstructs P hp v hv hb ht g r Y).2] at ho
  exact ⟨hi,ho⟩

theorem exists_nativeTwoSidedCollar_source_feedback
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃r₀ : ℝ,0<r₀ ∧ r₀≤1 ∧ ∀r : ℝ,0≤r → r≤r₀ → ∀p∈Λ,
      ∃T : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource,‖T‖≤2 ∧ ∀X,
        T X=X+nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g p) r (T X) ∧
        nativeL2FullPhysicalSourceCLM (T X).1=nativeL2FullPhysicalSourceCLM X.1+
          nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) (g p) r (T X) ∧
        nativeL2FullPhysicalSourceCLM (T X).2=nativeL2FullPhysicalSourceCLM X.2+
          nativeTwoSidedExteriorErrorCLM P hp v hv hb ht (g p) r (T X) ∧
        NativeCollarWeakGluing (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ (T X))
          (nativeTwoSidedExteriorJetCLM P hp v hv hb ht (T X)) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedCollarSourceError_linear_bound P hp v hv hb ht Λ g hB hρ
  refine ⟨min 1 (1/(2*C)),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro r hr hr0 p hp'
  have hK : ‖nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g p) r‖≤1/2 := by
    apply (hc r hr (hr0.trans (min_le_left _ _)) p hp').trans
    have he := mul_le_mul_of_nonneg_left (hr0.trans (min_le_right _ _)) hC.le
    exact he.trans_eq (by field_simp)
  let K := nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g p) r
  refine ⟨nativeTwoSidedFeedbackCLM K hK,nativeTwoSidedFeedback_norm K hK,fun X => ?_⟩
  have he := nativeTwoSidedCollarFeedback_physical_identity P hp v hv hb ht (g p) r hK X
  exact ⟨nativeTwoSidedFeedback_fixed K hK X,he.1,he.2,
    nativeTwoSidedSource_actual_weak_gluing P hp v hv hb ht _⟩

#print axioms nativeTwoSidedFeedback_fixed
#print axioms nativeTwoSidedFeedback_norm
#print axioms nativeTwoSidedFeedback_unique
#print axioms nativeTwoSidedCollarFeedback_physical_identity
#print axioms exists_nativeTwoSidedCollar_source_feedback
end Yamabe3.Analysis.SpherePolar
