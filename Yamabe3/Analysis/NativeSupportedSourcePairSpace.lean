import Yamabe3.Analysis.VectorL2MeasureRestriction
import Yamabe3.Analysis.NativeFiniteWindowSourceInverse

/-! The complete invariant source-pair space has an actual lower time
support constraint. The finite near inverse preserves that SAME space;
its closure is proved, not inferred from per-input support statements. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

def nativeSourcePairLowerRestrictionCLM (b:ℝ) : NativeTwoSidedSource →L[ℝ]
    Lp AngularSpectralSpace 2 (volume.restrict (Iio b)) :=
  (vectorL2MeasureRestrictCLM (H:=AngularSpectralSpace) Measure.restrict_le_self).comp
    (ContinuousLinearMap.snd ℝ _ _)

def nativeSupportedSourcePairSpace (b:ℝ) : Submodule ℝ NativeTwoSidedSource :=
  (nativeSourcePairLowerRestrictionCLM b).ker

instance nativeSupportedSourcePairSpace_closed (b:ℝ) :
    IsClosed (nativeSupportedSourcePairSpace b:Set NativeTwoSidedSource) :=
  (nativeSourcePairLowerRestrictionCLM b).isClosed_ker

instance nativeSupportedSourcePairSpace_complete (b:ℝ) : CompleteSpace (nativeSupportedSourcePairSpace b) := inferInstance

theorem nativeSupportedSourcePairSpace_mem_iff (b:ℝ) (X:NativeTwoSidedSource) :
    X∈nativeSupportedSourcePairSpace b ↔ ∀ᵐt:ℝ∂volume,t < b → X.2 t=0 := by
  change nativeSourcePairLowerRestrictionCLM b X=0 ↔ _
  have hco:(nativeSourcePairLowerRestrictionCLM b X:ℝ→AngularSpectralSpace)=ᵐ[volume.restrict (Iio b)]
      (X.2:ℝ→AngularSpectralSpace) := vectorL2MeasureRestrict_ae Measure.restrict_le_self X.2
  constructor
  · intro hz
    rw [hz] at hco
    have hf:(X.2:ℝ→AngularSpectralSpace)=ᵐ[volume.restrict (Iio b)]0 :=
      hco.symm.trans (Lp.coeFn_zero AngularSpectralSpace 2 _)
    exact (ae_restrict_iff' measurableSet_Iio).mp hf
  · intro hf
    apply Lp.ext
    have hfae:(X.2:ℝ→AngularSpectralSpace)=ᵐ[volume.restrict (Iio b)]0 :=
      (ae_restrict_iff' measurableSet_Iio).mpr hf
    exact hco.trans (hfae.trans (Lp.coeFn_zero AngularSpectralSpace 2 _).symm)

theorem exists_nativeSupportedFiniteWindow_source_inverse
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (m:ℕ) (hb0:b ≤ -(m:ℝ)/2-1) {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E)
    (hB:∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ε₀:ℝ,0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ε:ℝ,0 ≤ ε → ε ≤ ε₀ → ∀p∈Λ,
      ∃T:nativeSupportedSourcePairSpace b →L[ℝ] nativeSupportedSourcePairSpace b,
        ‖T‖ ≤ 2 ∧ ∀X,(T X).val=X.val+
          nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m (g p) ε (T X).val := by
  obtain ⟨ε₀,hε₀,hε₁,hi⟩:=exists_nativeFiniteWindow_source_inverse P hp v hv hb b ht m Λ g hB hρ
  refine ⟨ε₀,hε₀,hε₁,fun ε hε hε0 p hp'=>?_⟩
  obtain ⟨S,hS,hSv⟩:=hi ε hε hε0 p hp'
  let I:=(nativeSupportedSourcePairSpace b).subtypeL
  have hmem (X:nativeSupportedSourcePairSpace b):S X.val∈nativeSupportedSourcePairSpace b := by
    apply (nativeSupportedSourcePairSpace_mem_iff b _).mpr
    exact nativeFiniteWindow_fixed_preserves_lower_support P hp v hv hb b ht m (g p) ε X.val
      (S X.val) (hSv X.val) hb0 ((nativeSupportedSourcePairSpace_mem_iff b X.val).mp X.property)
  let T:=(S.comp I).codRestrict (nativeSupportedSourcePairSpace b) hmem
  refine ⟨T,?_,fun X=>hSv X.val⟩
  apply T.opNorm_le_bound (by norm_num)
  intro X
  exact S.le_of_opNorm_le hS X.val

#print axioms nativeSupportedSourcePairSpace_mem_iff
#print axioms exists_nativeSupportedFiniteWindow_source_inverse
end Yamabe3.Analysis.SpherePolar
