import Yamabe3.Analysis.NativeH4MatchedCollar
import Yamabe3.Analysis.NativeLowCauchyAllScaleOperators
import Yamabe3.Analysis.NativeExteriorShiftedFamilyOperators
import Yamabe3.Analysis.NativeScaledJetRepresentation

/-! The original H4 graph has ONE actual outer field at every scale.
The low compensation and the coupled high datum are both retained.
In particular this does not replace the outer field by an auxiliary H4
extension of its inner representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
variable (P:NativeHighPotential) {τ:ℝ} (ht:0 < τ)

def nativeH4GraphLowCauchyCoordinateCLM : HalfEndPhysicalH4Graph →L[ℝ] NativeLowCauchyCoordinates :=
  nativeLowCauchyCoordinateCLM.comp
    (nativeH4GraphAngularValueCLM.prod (-nativeH4GraphAngularNormalCLM-(1/2:ℝ) • nativeH4GraphAngularValueCLM))

def nativeH4MatchedExteriorAllScaleJet (x:HalfEndPhysicalH4Graph) (s:ℝ) : nativeCollarJetClosure :=
  nativeLowCauchyAllScaleJet ht (nativeH4GraphLowCauchyCoordinateCLM x) s+
    nativeExteriorShiftedJet (fullBubbleHighPotential (-τ)) s
      (nativeH4GraphExteriorDatumCLM (fullBubbleHighPotential (-τ)) P x)
      (nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P x)

theorem nativeH4MatchedExteriorAllScale_zero (x:HalfEndPhysicalH4Graph) :
    nativeH4MatchedExteriorAllScaleJet P ht x 0=nativeH4MatchedExteriorJetCLM P ht x := by
  unfold nativeH4MatchedExteriorAllScaleJet nativeLowCauchyAllScaleJet
  rw [nativeFiniteAllScaleJet_zero_eq,nativeExteriorShiftedJet_zero_eq_original]
  change _=nativeLowCauchyCollarCLM ht
    (nativeH4GraphAngularValueCLM x,-nativeH4GraphAngularNormalCLM x-(1/2:ℝ) • nativeH4GraphAngularValueCLM x)+_
  rw [nativeLowCauchyCollarCLM_eq]
  rfl

theorem exists_nativeH4MatchedExteriorAllScale_bound :
    ∃C:ℝ,0 ≤ C ∧ ∀s:ℝ,s ≤ 0 →
      ∃J:HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure,‖J‖ ≤ C ∧
        ∀x,J x=nativeH4MatchedExteriorAllScaleJet P ht x s := by
  obtain ⟨C₀,hC₀,h₀⟩:=exists_nativeLowCauchyAllScaleJetCLM ht
  obtain ⟨C₁,hC₁,h₁⟩:=exists_nativeExteriorShiftedFamilyJetCLM (fullBubbleHighPotential (-τ))
    (nativeH4GraphExteriorDatumCLM (fullBubbleHighPotential (-τ)) P)
    (nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P)
    (nativeH4GraphExteriorDatum_spectral_bound P (fullBubbleHighPotential (-τ)))
  let D:=nativeH4GraphLowCauchyCoordinateCLM
  refine ⟨C₀*‖D‖+C₁,by positivity,fun s hs=>?_⟩
  obtain ⟨J₀,hJ₀,hJ₀v⟩:=h₀ s hs
  obtain ⟨J₁,hJ₁,hJ₁v⟩:=h₁ s hs
  refine ⟨J₀.comp D+J₁,?_,fun x=>?_⟩
  · apply (J₀.comp D+J₁).opNorm_le_bound (by positivity)
    intro x
    change ‖J₀ (D x)+J₁ x‖ ≤ _
    have h₀x:‖J₀ (D x)‖ ≤ C₀*‖D‖*‖x‖:=
      ((J₀.le_of_opNorm_le hJ₀ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm x) hC₀)).trans_eq (by ring)
    exact (norm_add_le _ _).trans ((add_le_add h₀x (J₁.le_of_opNorm_le hJ₁ x)).trans_eq (by ring))
  · change J₀ (D x)+J₁ x=_
    rw [hJ₀v,hJ₁v]
    rfl

theorem exists_nativeH4MatchedExteriorAllScale_same_field (x:HalfEndPhysicalH4Graph) :
    ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧
      ∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht x s) s w := by
  let d:=nativeH4GraphLowCauchyCoordinateCLM x
  let q:=fun i t=>nativeLowCauchyQ ht d i (τ+t)
  have hq:∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i):=fun i hi=>
    (nativeLowCauchyQ_C2 ht d i hi).comp (contDiff_const.add contDiff_id)
  let B:=fullBubbleHighPotential (-τ)
  let datum:=nativeH4GraphExteriorDatumCLM B P x
  obtain ⟨w,hw,hwa,_⟩:=nativePoissonExteriorCurve_joint_representative B datum
  refine ⟨fun p=>finiteAngular nativeLowIndexFinset q p+w p,
    (nativeFiniteAngular_continuous nativeLowIndexFinset q hq).measurable.add hw.measurable,fun s=>?_⟩
  apply NativeScaledJetRep.add
  · change (↑(nativeFiniteAllScaleJet nativeLowIndexFinset q hq s).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] _
    simpa only [finitePhysical_eq_lift] using nativeFiniteAllScaleJet_same_field nativeLowIndexFinset q hq s
  · exact nativeExteriorShiftedValue_same_field B s datum
      (nativeH4GraphExteriorDatum_regular B P x) hw.measurable hwa

#print axioms nativeH4MatchedExteriorAllScale_zero
#print axioms exists_nativeH4MatchedExteriorAllScale_bound
#print axioms exists_nativeH4MatchedExteriorAllScale_same_field
end Yamabe3.Analysis.UniformElliptic
