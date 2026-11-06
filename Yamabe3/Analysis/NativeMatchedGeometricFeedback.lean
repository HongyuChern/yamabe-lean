import Yamabe3.Analysis.NativeMatchedGeometricSource
import Yamabe3.Analysis.NativeGlobalSourceFeedback

/-! A real full-mode source inverse, with one radius chosen before the
orbit and phase. Its fixed point corrects the actual full geometric error. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

theorem exists_uniform_nativeMatchedGeometricSource_small_radius
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ,0 ≤ ε → ε ≤ ε₀ → ∀ a ∈ Λ, 
        ‖nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε‖≤1/2 := by
  obtain ⟨C,hC,hc⟩ := exists_uniform_nativeMatchedGlobalGeometricSource_bound hκ0 hκ1 Λ g hB hρ
  refine ⟨min 1 (1/(2*C)),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro B p hp ε hε hε0 a ha
  apply (hc B p hp ε hε (hε0.trans (min_le_left _ _)) a ha).trans
  have he := mul_le_mul_of_nonneg_left (hε0.trans (min_le_right _ _)) hC.le
  exact he.trans_eq (by field_simp)

theorem exists_uniform_nativeMatchedGeometricSource_feedback
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ,0 ≤ ε → ε ≤ ε₀ → ∀ a ∈ Λ, 
      ∃ T : NativeSpectralSourceL2 →L[ℝ] NativeSpectralSourceL2,
        ‖T‖≤2 ∧ (∀ f,T f=f+nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε (T f)) ∧
        (∀ f F,F=f+nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε F → F=T f) := by
  obtain ⟨ε₀,hε₀,hε1,h⟩ := exists_uniform_nativeMatchedGeometricSource_small_radius hκ0 hκ1 Λ g hB hρ
  refine ⟨ε₀,hε₀,hε1,fun B p hp ε hε hε0 a ha => ?_⟩
  let K := nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε
  have hK : ‖K‖≤1/2 := h B p hp ε hε hε0 a ha
  exact ⟨nativeSourceFeedbackCLM K hK,nativeSourceFeedback_norm K hK,
    nativeSourceFeedback_fixed K hK,nativeSourceFeedback_unique K hK⟩

#print axioms exists_uniform_nativeMatchedGeometricSource_small_radius
#print axioms exists_uniform_nativeMatchedGeometricSource_feedback
end Yamabe3.Analysis.SpherePolar
