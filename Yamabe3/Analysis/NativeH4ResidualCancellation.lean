import Yamabe3.Analysis.NativeH4CorrectedMatchedField
import Yamabe3.Analysis.NativeSupportedOuterNativeEquation
import Yamabe3.Analysis.NativeMatchedJetEquations

/-! The geometric residual of the original matched H4 field is cancelled
by the same actual two-sided correction. The inner equality retains full
shell weights; the outer equality retains both computed finite low-mode
compensations and the physical factor eight. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeTwoSidedJacobianRowCLM
  nativeH4MatchedGeometricSourceTerm
private theorem operator_inner_hasSum {X Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (T : ℕ → X →L[ℝ] Z) (hs : Summable T) (F : X) (G : Z) :
    HasSum (fun n => inner ℝ (T n F) G) (inner ℝ ((∑'n,T n) F) G) := by
  let ev := ContinuousLinearMap.apply ℝ Z F
  have h : HasSum (fun n => inner ℝ G (T n F)) (inner ℝ G ((∑'n,T n) F)) :=
    (hs.hasSum.mapL ev).mapL (innerSL ℝ G)
  simpa only [real_inner_comm] using h

variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v₀ : ℝ→ℝ) (hv : Continuous v₀) (hb : ∀t,0≤v₀ t ∧ v₀ t≤1)
  (b : ℝ) {τ : ℝ} (ht : 0<τ)

theorem nativeH4MatchedResidual_pairing_hasSum
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (x : HalfEndPhysicalH4Graph) (G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    HasSum (fun n => inner ℝ (nativeH4MatchedGeometricSourceTerm (fullBubbleHighPotential (-τ)) P hp (g a) ε n x) G)
      (inner ℝ (nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε x) G) := by
  have hs := nativeH4MatchedGeometricSourceTerm_summable (fullBubbleHighPotential (-τ)) P hp Λ g hB hρ ε hε hε1 a ha
  exact operator_inner_hasSum _ hs x G

theorem nativeH4MatchedResidual_cancellation
    (hpot : P.potential=delaunayPhasePotentialBCF v₀ hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (hY : Y=nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε x+
      nativeSupportedTwoSidedGlobalSourceCLM P hp v₀ hv hb b ht (g a) ε Y)
    (G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (hG0 : ∀ᵐt : ℝ ∂volume,t≤0 → G t=0) :
    HasSum (fun n => inner ℝ (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeH4MatchedGeometricRowCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε
        (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n) x+
        nativeTwoSidedJacobianRowCLM P hp v₀ hv hb τ (g a) ε (nativeLogShellCenter n) Y)) G) 0 := by
  have h1 := nativeH4MatchedResidual_pairing_hasSum P hp (τ:=τ) Λ g hB hρ ε hε hε1 a ha x G
  have h2 := nativeSupportedTwoSidedGlobal_fixed_pairing P hp v₀ hv hb b ht hpot Λ g hB hρ ε hε hε1 a ha
    (nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε x) Y hY G hG0
  have he : inner ℝ (nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε x) G+
      -inner ℝ (nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε x).1 G=0 := by
    change inner ℝ _ G+ -inner ℝ _ G=0
    exact add_neg_cancel _
  have hsum := h1.add h2
  rw [he] at hsum
  simpa only [map_add,inner_add_left,nativeH4MatchedGeometricSourceTerm,ContinuousLinearMap.comp_apply] using hsum

theorem nativeH4MatchedResidual_outer_equation
    (g : RiemannianMetric 3 E) (ε : ℝ) (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (hb0 : b≤ -(1/2:ℝ))
    (hY : Y=nativeH4MatchedGlobalResidualCLM P hp ht g ε x+
      nativeSupportedTwoSidedGlobalSourceCLM P hp v₀ hv hb b ht g ε Y) :
    let B := fullBubbleHighPotential (-τ)
    let K := nativeH4MatchedExteriorJetCLM P ht x+nativeSupportedTwoSidedExteriorJetCLM P hp v₀ hv hb b ht Y
    (nativeExteriorNativeJacobianCLM g ε (nativePoissonExteriorPotential B) K.val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar]
      (fun y => nativeBubbleCollarCompensation τ
        (nativeCauchyCompensationData ht (nativeH4GraphAngularValueCLM x) (nativeH4GraphAngularNormalCLM x)) y+
        nativeBubbleCollarCompensation τ (nativeSupportedTwoSidedExteriorCompensation P hp v₀ hv hb b ht Y) y) := by
  let B := fullBubbleHighPotential (-τ)
  let K := nativeH4MatchedExteriorJetCLM P ht x
  let L := nativeSupportedTwoSidedExteriorJetCLM P hp v₀ hv hb b ht Y
  let V := nativePoissonExteriorPotential B
  let E₀ := nativeNegativeCollarRestrictionCLM (nativeH4MatchedExteriorErrorCLM P ht g ε x)
  have hsupport : ∀ᵐt : ℝ ∂volume,t<b → (nativeH4MatchedGlobalResidualCLM P hp ht g ε x).2 t=0 := by
    filter_upwards [nativeFullCollarSourceReturn_time_support (nativeH4MatchedExteriorErrorCLM P ht g ε x)] with t hs
    intro htb
    apply hs
    intro hc
    linarith [hc.1]
  have hc := nativeSupportedTwoSidedGlobal_outer_native_equation P hp v₀ hv hb b ht g ε
    (nativeH4MatchedGlobalResidualCLM P hp ht g ε x) Y hb0 hsupport hY
  have hm := nativeCauchyOuter_computed_source ht (nativeH4GraphAngularValueCLM x) (nativeH4GraphAngularNormalCLM x)
    (nativeH4GraphExteriorDatumCLM B P x) (nativeH4GraphExteriorDatum_regular B P x)
  have hsource : nativeL2FullPhysicalSourceCLM (nativeH4MatchedGlobalResidualCLM P hp ht g ε x).2=
      nativeH4MatchedExteriorErrorCLM P ht g ε x := nativeFullCollarSourceReturn_right_inverse _
  rw [hsource] at hc
  change (nativeExteriorModelJacobianCLM V K.val : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] _ at hm
  have hk : nativeExteriorNativeJacobianCLM g ε V K.val=nativeExteriorModelJacobianCLM V K.val+(8:ℝ) • E₀ :=
    nativeExteriorNativeJacobian_eq_model_add_residual g ε V K.val
  dsimp only
  rw [Submodule.coe_add,map_add]
  change ((nativeExteriorNativeJacobianCLM g ε V K.val+nativeExteriorNativeJacobianCLM g ε V L.val : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) : E→ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] _
  rw [hk]
  filter_upwards [Lp.coeFn_add (nativeExteriorModelJacobianCLM V K.val+(8:ℝ) • E₀)
      (nativeExteriorNativeJacobianCLM g ε V L.val),
    Lp.coeFn_add (nativeExteriorModelJacobianCLM V K.val) ((8:ℝ) • E₀),
    Lp.coeFn_smul (8:ℝ) E₀,hm,hc] with y ha hk he hm hc
  rw [ha]
  change (nativeExteriorModelJacobianCLM V K.val+(8:ℝ) • E₀ : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) y+
    nativeExteriorNativeJacobianCLM g ε V L.val y=_
  rw [hk]
  change nativeExteriorModelJacobianCLM V K.val y+((8:ℝ) • E₀ : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) y+
    nativeExteriorNativeJacobianCLM g ε V L.val y=_
  change ((8:ℝ) • E₀ : Lp ℝ 2 (volume.restrict nativeNegativeEntranceCollar)) y=8*E₀ y at he
  change nativeExteriorNativeJacobianCLM g ε V L.val y= -8*E₀ y+
    nativeBubbleCollarCompensation τ (nativeSupportedTwoSidedExteriorCompensation P hp v₀ hv hb b ht Y) y at hc
  rw [he,hm,hc]
  change _+8*E₀ y+(-8*E₀ y+_)=_
  ring

#print axioms nativeH4MatchedResidual_pairing_hasSum
#print axioms nativeH4MatchedResidual_cancellation
#print axioms nativeH4MatchedResidual_outer_equation
end Yamabe3.Analysis.UniformElliptic
