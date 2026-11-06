import Yamabe3.Analysis.NativeGlobalSourcePairing
import Yamabe3.Analysis.SmallErrorBoundedSolver

/-! Actual plus-sign source feedback F=f+K F. The sign follows from
J_native u=-F+E u, and is implemented by the verified minus solver with
-E. This is not yet an assertion that all native low-mode residuals vanish. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

abbrev NativeSpectralSourceL2 := Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)

theorem nativeSourceFeedback_small (K : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2)
    (hK : ‖K‖≤1/2) : ‖ContinuousLinearMap.id ℝ NativeSpectralSourceL2‖*‖-K‖≤1/2 := by
  rw [norm_neg]
  exact (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le) (norm_nonneg K)).trans
    (by simpa only [one_mul] using hK)

def nativeSourceFeedbackCLM (K : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2)
    (hK : ‖K‖≤1/2) : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2 :=
  smallErrorSolutionCLM (ContinuousLinearMap.id ℝ _) (-K) (nativeSourceFeedback_small K hK)

theorem nativeSourceFeedback_fixed (K : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2)
    (hK : ‖K‖≤1/2) (f : NativeSpectralSourceL2) :
    nativeSourceFeedbackCLM K hK f=f+K (nativeSourceFeedbackCLM K hK f) := by
  exact (smallErrorSolution_fixed (ContinuousLinearMap.id ℝ _) (-K)
    (nativeSourceFeedback_small K hK) f).symm.trans (by simp only
      [ContinuousLinearMap.id_apply,ContinuousLinearMap.neg_apply,sub_neg_eq_add];rfl)

theorem nativeSourceFeedback_norm (K : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2)
    (hK : ‖K‖≤1/2) : ‖nativeSourceFeedbackCLM K hK‖≤2 := by
  exact (smallErrorSolutionCLM_norm _ _ _).trans (by
    nlinarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := NativeSpectralSourceL2)])

theorem nativeSourceFeedback_unique (K : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2)
    (hK : ‖K‖≤1/2) (f F : NativeSpectralSourceL2) (hF : F=f+K F) :
    F=nativeSourceFeedbackCLM K hK f := by
  symm
  apply smallErrorSolution_unique (ContinuousLinearMap.id ℝ _) (-K) (nativeSourceFeedback_small K hK) f F
  simpa only [ContinuousLinearMap.id_apply,ContinuousLinearMap.neg_apply,sub_neg_eq_add] using hF.symm

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

theorem exists_nativeGlobalGeometricSource_small_radius
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ,0≤ε → ε≤ε₀ → ∀ p∈Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) → ∀ phase,
      ‖nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase‖≤1/2 := by
  obtain ⟨C,hC,hc⟩ := exists_nativeGlobalGeometricSource_norm_bound P hplus Λ g hB hρ
  refine ⟨min 1 (1/(2*C)),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro ε hε hε0 p hp v hv hvb hvo phase
  apply (hc ε hε (hε0.trans (min_le_left _ _)) p hp v hv hvb hvo phase).trans
  have he := hε0.trans (min_le_right _ _)
  have he' := mul_le_mul_of_nonneg_left he hC.le
  have hc' : C*(1/(2*C))=1/2 := by field_simp
  exact he'.trans_eq hc'

theorem exists_nativeGlobalGeometricSource_feedback
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ,0≤ε → ε≤ε₀ → ∀ p∈Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) → ∀ phase,
      ∃ T : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2,
        ‖T‖≤2 ∧ (∀ f,T f=f+nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase (T f)) ∧
        (∀ f F,F=f+nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase F → F=T f) := by
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_nativeGlobalGeometricSource_small_radius P hplus Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,fun ε hε hε0 p hp v hv hvb hvo phase => ?_⟩
  let K := nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase
  have hK : ‖K‖≤1/2 := h ε hε hε0 p hp v hv hvb hvo phase
  exact ⟨nativeSourceFeedbackCLM K hK,nativeSourceFeedback_norm K hK,
    nativeSourceFeedback_fixed K hK,nativeSourceFeedback_unique K hK⟩

#print axioms nativeSourceFeedback_fixed
#print axioms nativeSourceFeedback_norm
#print axioms nativeSourceFeedback_unique
#print axioms exists_nativeGlobalGeometricSource_small_radius
#print axioms exists_nativeGlobalGeometricSource_feedback
end Yamabe3.Analysis.SpherePolar
