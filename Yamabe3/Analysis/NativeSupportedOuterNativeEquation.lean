import Yamabe3.Analysis.NativeSupportedGlobalFeedback

/-! The actual native outer collar equation for the same supported global
feedback point. Its finite low compensation is retained, and source support
is proved invariant before applying the original-source reconstruction. -/
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
  (b : ℝ) {t₀ : ℝ} (ht : 0<t₀)

def nativeSupportedTwoSidedExteriorCompensation (X : NativeTwoSidedSource) : AngularIndex→ℝ :=
  nativeSupportedBubbleExteriorInhomogeneousCompensation b ht (nativeTwoSidedExteriorDataCLM P hp v hv hb X)

theorem nativeSupportedTwoSidedExterior_model_source (X : NativeTwoSidedSource)
    (hX : ∀ᵐt : ℝ ∂volume,t<b → X.2 t=0) :
    (nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht X).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht X) x) := by
  rw [nativeSupportedTwoSidedExteriorJetCLM_eq,Submodule.coe_add,map_add,nativeExteriorModelJacobian_high_zero,add_zero]
  exact nativeSupportedBubbleExteriorInhomogeneousJet_source b ht X.2
    (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1) hX

theorem nativeSupportedTwoSidedExterior_native_equation_of_source_identity (g : RiemannianMetric 3 E) (r : ℝ)
    (X Y : NativeTwoSidedSource)
    (hYs : ∀ᵐt : ℝ ∂volume,t<b → Y.2 t=0)
    (he : nativeL2FullPhysicalSourceCLM Y.2=nativeL2FullPhysicalSourceCLM X.2+
      nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g r Y) :
    (nativeExteriorNativeJacobianCLM g r (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht Y).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht Y) x) := by
  let K := nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht Y
  let V := nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))
  let M := nativeExteriorModelJacobianCLM V K.val
  let Err := nativeSupportedTwoSidedExteriorErrorCLM P hp v hv hb b ht g r Y
  let R := (8:ℝ) • nativeNegativeCollarRestrictionCLM Err
  let SY := (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2)
  let SX := (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2)
  have hsum : SY+R=SX := by
    dsimp only [SY,R,SX]
    rw [he,map_add,smul_add]
    module
  have hsae := Lp.coeFn_add SY R
  rw [hsum] at hsae
  have hm := nativeSupportedTwoSidedExterior_model_source P hp v hv hb b ht Y hYs
  rw [nativeExteriorNativeJacobian_eq_model_add_residual]
  change ((M+R : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] _
  filter_upwards [Lp.coeFn_add M R,hm,hsae,
    Lp.coeFn_smul (-8:ℝ) (nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2)),
    Lp.coeFn_smul (-8:ℝ) (nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2))]
    with x ha hm hs hy hx
  rw [ha]
  change M x+R x=_
  change M x= -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2) : E→ℝ) x+
    nativeBubbleCollarCompensation t₀ (nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht Y) x at hm
  change SX x=SY x+R x at hs
  change SY x= -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM Y.2) : E→ℝ) x at hy
  change SX x= -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x at hx
  rw [hy,hx] at hs
  rw [hm]
  linarith only [hs]

theorem nativeSupportedTwoSidedGlobal_outer_native_equation (g : RiemannianMetric 3 E) (ε : ℝ)
    (X Y : NativeTwoSidedSource) (hb0 : b≤ -(1/2:ℝ))
    (hX : ∀ᵐt : ℝ ∂volume,t<b → X.2 t=0) (hY : Y=X+nativeSupportedTwoSidedGlobalSourceCLM P hp v hv hb b ht g ε Y) :
    (nativeExteriorNativeJacobianCLM g ε (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht Y).val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun x => -8*(nativeNegativeCollarRestrictionCLM (nativeL2FullPhysicalSourceCLM X.2) : E→ℝ) x+
        nativeBubbleCollarCompensation t₀ (nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht Y) x) :=
  nativeSupportedTwoSidedExterior_native_equation_of_source_identity P hp v hv hb b ht g ε X Y
    (nativeSupportedTwoSidedGlobal_outer_source_lower_support P hp v hv hb b ht g ε X Y hY hb0 hX)
    (nativeSupportedTwoSidedGlobal_outer_source_identity P hp v hv hb b ht g ε X Y hY)


#print axioms nativeSupportedTwoSidedExterior_model_source
#print axioms nativeSupportedTwoSidedExterior_native_equation_of_source_identity
#print axioms nativeSupportedTwoSidedGlobal_outer_native_equation
end Yamabe3.Analysis.SpherePolar
