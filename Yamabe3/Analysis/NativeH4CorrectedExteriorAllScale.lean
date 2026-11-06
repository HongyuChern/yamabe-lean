import Yamabe3.Analysis.NativeH4MatchedExteriorAllScale
import Yamabe3.Analysis.NativeH4CorrectedMatchedField
import Yamabe3.Analysis.NativeSupportedTwoSidedAllScaleOperators
import Yamabe3.Analysis.NativeSupportedTwoSidedExteriorField

/-! The ORIGINAL weighted-source baseline plus its actual residual
correction has one exterior field at every scale, with a bounded linear
jet family. No original H2 source is coerced into whole-time L2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1)
  (b:ℝ) {τ:ℝ} (ht:0 < τ)
  (T:HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource)

def nativeH4CorrectedExteriorAllScaleJet (x:HalfEndPhysicalH4Graph) (s:ℝ) : nativeCollarJetClosure :=
  nativeH4MatchedExteriorAllScaleJet P ht x s+
    nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (T x) s

theorem nativeH4CorrectedExteriorAllScale_zero (x:HalfEndPhysicalH4Graph) :
    nativeH4CorrectedExteriorAllScaleJet P hp v hv hb b ht T x 0=
      nativeH4CorrectedExteriorJetCLM P hp v hv hb b ht T x := by
  unfold nativeH4CorrectedExteriorAllScaleJet
  rw [nativeH4MatchedExteriorAllScale_zero,nativeSupportedTwoSidedExteriorAllScale_zero_eq]
  rfl

theorem exists_nativeH4CorrectedExteriorAllScale_bound :
    ∃C:ℝ,0 ≤ C ∧ ∀s:ℝ,s ≤ 0 →
      ∃J:HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure,‖J‖ ≤ C ∧
        ∀x,J x=nativeH4CorrectedExteriorAllScaleJet P hp v hv hb b ht T x s := by
  obtain ⟨C₀,hC₀,h₀⟩:=exists_nativeH4MatchedExteriorAllScale_bound P ht
  obtain ⟨C₁,hC₁,h₁⟩:=exists_nativeSupportedTwoSided_all_scale_CLM P hp v hv hb b ht
  refine ⟨C₀+C₁*‖T‖,by positivity,fun s hs=>?_⟩
  obtain ⟨J₀,hJ₀,hJ₀v⟩:=h₀ s hs
  obtain ⟨J₁,hJ₁,hJ₁v⟩:=h₁ s hs
  refine ⟨J₀+J₁.comp T,?_,fun x=>?_⟩
  · apply (J₀+J₁.comp T).opNorm_le_bound (by positivity)
    intro x
    change ‖J₀ x+J₁ (T x)‖ ≤ _
    have h₁x:‖J₁ (T x)‖ ≤ C₁*‖T‖*‖x‖:=
      ((J₁.le_of_opNorm_le hJ₁ _).trans
        (mul_le_mul_of_nonneg_left (T.le_opNorm x) hC₁)).trans_eq (by ring)
    exact (norm_add_le _ _).trans ((add_le_add (J₀.le_of_opNorm_le hJ₀ x) h₁x).trans_eq (by ring))
  · change J₀ x+J₁ (T x)=_
    rw [hJ₀v,hJ₁v]
    rfl

theorem exists_nativeH4CorrectedExteriorAllScale_same_field (x:HalfEndPhysicalH4Graph) :
    ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧
      ∀s:ℝ,NativeScaledJetRep (nativeH4CorrectedExteriorAllScaleJet P hp v hv hb b ht T x s) s w := by
  obtain ⟨w,hw,ha⟩:=exists_nativeH4MatchedExteriorAllScale_same_field P ht x
  obtain ⟨q,hq,_,hqa⟩:=exists_nativeSupportedOuter_same_field_all_scale b ht (T x).2
    (nativeLowL2AngularCLM v hv hb (T x).1 0) (nativeFullL2NormalAngularCLM P hp v hv hb (T x).1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ (T x))
    (nativeTwoSidedSourceSigma_regular P hp v hv hb τ (T x))
  exact ⟨fun p=>w p+q p,hw.add hq,fun s=>(ha s).add (hqa s).1⟩

#print axioms nativeH4CorrectedExteriorAllScale_zero
#print axioms exists_nativeH4CorrectedExteriorAllScale_bound
#print axioms exists_nativeH4CorrectedExteriorAllScale_same_field
end Yamabe3.Analysis.UniformElliptic
