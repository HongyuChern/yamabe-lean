import Yamabe3.Analysis.NativeTwoSidedCollarFeedback

/-! The same feedback-corrected exterior jet solves the actual native
collar equation for the original exterior source, with its finite low
compensation explicit. The geometric residual cancels by the proved
physical source reconstruction, not by suppressing a projected error. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
  {t₀ : ℝ} (ht : 0<t₀)

def nativeTwoSidedExteriorCompensation (X : NativeTwoSidedSource) : AngularIndex→ℝ :=
  nativeBubbleExteriorInhomogeneousCompensation ht (nativeTwoSidedExteriorDataCLM P hp v hv hb X)

theorem nativeTwoSidedExterior_model_source (X : NativeTwoSidedSource) :
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeTwoSidedExteriorJetCLM P hp v hv hb ht X).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeTwoSidedExteriorCompensation P hp v hv hb ht X) x) := by
  rw [nativeTwoSidedExteriorJetCLM_eq,Submodule.coe_add,map_add,nativeExteriorModelJacobian_high_zero,add_zero]
  exact nativeBubbleExteriorInhomogeneousJet_source ht X.2
    (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)

theorem nativeTwoSidedExterior_feedback_native_equation (g : RiemannianMetric 3 E) (r : ℝ)
    (hK : ‖nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r‖≤1/2) (X : NativeTwoSidedSource) :
    let Y := nativeTwoSidedFeedbackCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r) hK X
    let K := nativeTwoSidedExteriorJetCLM P hp v hv hb ht Y
    (nativeExteriorNativeJacobianCLM g r (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) K.val : E→ℝ)
      =ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeTwoSidedExteriorCompensation P hp v hv hb ht Y) x) := by
  dsimp only
  let Y := nativeTwoSidedFeedbackCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r) hK X
  let K := nativeTwoSidedExteriorJetCLM P hp v hv hb ht Y
  let V := nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))
  let M := nativeExteriorModelJacobianCLM V K.val
  let Err := nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g r Y
  let R := (8:ℝ) • nativeNegativeCollarRestrictionCLM Err
  let SY := (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2)
  let SX := (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2)
  have he : nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM X.2+Err :=
    (nativeTwoSidedCollarFeedback_physical_identity P hp v hv hb ht g r hK X).2
  have hsum : SY+R=SX := by
    dsimp only [SY,R,SX]
    rw [he,map_add,smul_add]
    module
  have hsae := Lp.coeFn_add SY R
  rw [hsum] at hsae
  have hm := nativeTwoSidedExterior_model_source P hp v hv hb ht Y
  change (nativeExteriorNativeJacobianCLM g r V K.val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] _
  rw [nativeExteriorNativeJacobian_eq_model_add_residual]
  change ((M+R : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] _
  filter_upwards [Lp.coeFn_add M R,hm,hsae,
    Lp.coeFn_smul (-8:ℝ) (nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2)),
    Lp.coeFn_smul (-8:ℝ) (nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2))]
    with x ha hm hs hy hx
  rw [ha]
  change M x+R x=_
  change M x= -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2) : E→ℝ) x+
    nativeBubbleCollarCompensation t₀ (nativeTwoSidedExteriorCompensation P hp v hv hb ht Y) x at hm
  change SX x=SY x+R x at hs
  change SY x= -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2) : E→ℝ) x at hy
  change SX x= -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x at hx
  rw [hy,hx] at hs
  rw [hm]
  linarith only [hs]

#print axioms nativeTwoSidedExterior_model_source
#print axioms nativeTwoSidedExterior_feedback_native_equation
end Yamabe3.Analysis.SpherePolar
