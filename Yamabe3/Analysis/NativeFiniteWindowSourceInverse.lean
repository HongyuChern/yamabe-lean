import Yamabe3.Analysis.NativeFiniteWindowGeometricFeedback
import Yamabe3.Analysis.NativeOuterWindowSourceSupport

/-! A genuine bounded inverse on one complete source pair for the full
inner half-end plus a FIXED finite exterior window. The fixed support
bound is preserved. The far/global block is a separate remaining step. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)

theorem exists_nativeFiniteWindow_source_inverse
    (m:ℕ) {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E)
    (hB:∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ε₀:ℝ,0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ε:ℝ,0 ≤ ε → ε ≤ ε₀ → ∀p∈Λ,
      ∃T:NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource,‖T‖ ≤ 2 ∧ ∀X,
        T X=X+nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m (g p) ε (T X) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hbnd⟩:=exists_nativeFiniteWindowGlobalSource_bound P hp v hv hb b ht m Λ g hB hρ
  refine ⟨min δ (1/(2*C)),lt_min hδ (by positivity),(min_le_left _ _).trans hδ1,?_⟩
  intro ε hε hε₀ p hp'
  let K:=nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m (g p) ε
  have hK:‖K‖ ≤ 1/2 := by
    apply (hbnd ε hε (hε₀.trans (min_le_left _ _)) p hp').trans
    exact (mul_le_mul_of_nonneg_left (hε₀.trans (min_le_right _ _)) hC.le).trans_eq (by field_simp)
  exact ⟨nativeTwoSidedFeedbackCLM K hK,nativeTwoSidedFeedback_norm K hK,nativeTwoSidedFeedback_fixed K hK⟩

theorem nativeFiniteWindow_fixed_preserves_lower_support
    (m:ℕ) (g:RiemannianMetric 3 E) (ε:ℝ) (X Y:NativeTwoSidedSource)
    (hY:Y=X+nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m g ε Y)
    (hb0:b ≤ -(m:ℝ)/2-1) (hX:∀ᵐt:ℝ∂volume,t < b → X.2 t=0) :
    ∀ᵐt:ℝ∂volume,t < b → Y.2 t=0 := by
  have he:=congrArg Prod.snd hY
  change Y.2=X.2+nativeFiniteOuterWindowSourceCLM m
    (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y at he
  rw [he]
  filter_upwards [Lp.coeFn_add X.2 (nativeFiniteOuterWindowSourceCLM m
      (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y),hX,
    nativeFiniteOuterWindowSource_lower_support m
      (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y] with t ha hx hz
  intro htb
  rw [ha]
  change X.2 t+nativeFiniteOuterWindowSourceCLM m
    (fun i=>nativeFiniteWindowGeometricRowCLM P hp v hv hb b ht g ε i) Y t=0
  rw [hx htb,hz (htb.trans_le hb0),add_zero]

#print axioms exists_nativeFiniteWindow_source_inverse
#print axioms nativeFiniteWindow_fixed_preserves_lower_support
end Yamabe3.Analysis.SpherePolar
