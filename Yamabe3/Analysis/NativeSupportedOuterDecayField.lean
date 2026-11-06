import Yamabe3.Analysis.NativeSupportedOuterCurve

/-! The complete outer decay curve is the same field as every previously
constructed exterior jet, including the compensated low modes. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

private theorem angular_add_rep {f h:S→ℝ} {a b:AngularL2}
    (hf:f=ᵐ[angularVolume](a:S→ℝ)) (hh:h=ᵐ[angularVolume](b:S→ℝ)) :
    (fun θ=>f θ+h θ)=ᵐ[angularVolume]((a+b:AngularL2):S→ℝ) := by
  have hab:=(ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_add a b)
  filter_upwards [hf,hh,hab] with θ hf hh hab
  rw [hf,hh]
  exact (hab (mem_univ θ)).symm

private theorem angular_sub_rep {f h:S→ℝ} {a b:AngularL2}
    (hf:f=ᵐ[angularVolume](a:S→ℝ)) (hh:h=ᵐ[angularVolume](b:S→ℝ)) :
    (fun θ=>f θ-h θ)=ᵐ[angularVolume]((a-b:AngularL2):S→ℝ) := by
  have hab:=(ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_sub a b)
  filter_upwards [hf,hh,hab] with θ hf hh hab
  rw [hf,hh]
  exact (hab (mem_univ θ)).symm

theorem exists_nativeSupportedOuter_same_curve_all_scale (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)) :
    ∃w:ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ:Set E) ∧
      (∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ)) ∧
      ∀s:ℝ,NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w ∧
        MemWkp 2 2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 nativePoissonEntranceCollar := by
  obtain ⟨wp,hwp,hpa,hjp⟩:=nativeBubbleFullSupported_same_field τ b F
  let P:=fullBubbleHighPotential τ
  let B:=fullBubbleHighPotential (-τ)
  let a:=nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ) F
  let ha:=(nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ) F).2.1
  obtain ⟨wa,hwa,haa,_,hja⟩:=exists_nativeExteriorPoisson_same_field_localH2 B a ha
  obtain ⟨ws,hws,hsa,_,hjs⟩:=exists_nativeExteriorPoisson_same_field_localH2 B σ hσ
  let q:=nativeSupportedLowCauchyCoefficients b ht F d n
  let hq:=nativeSupportedLowCauchyCoefficients_C2 b ht F d n
  let wc:=finiteAngular nativeLowIndexFinset q
  have hwc:=(nativeFiniteAngular_continuous nativeLowIndexFinset q hq).measurable
  let w:=fun z=>(wp z+wc z)-wa z+ws z
  have hj(s:ℝ):NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w:=by
    have hp:NativeScaledJetRep (nativeSupportedParticularJet τ b s F) s wp:=hjp s
    have hc:NativeScaledJetRep (nativeSupportedLowCauchyAllScaleJet b ht F d n s) s wc:=by
      change ((nativeFiniteAllScaleJet nativeLowIndexFinset q hq s).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x=>Real.exp (3*s/2)*cylinderLift (finiteAngular nativeLowIndexFinset q) (Real.exp (-s) • x))
      simpa only [finitePhysical_eq_lift] using nativeFiniteAllScaleJet_same_field nativeLowIndexFinset q hq s
    exact ((hp.add hc).sub (hja s).1).add (hjs s).1
  have hm(s:ℝ):=nativeCollarJetClosure_memH2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s)
  refine ⟨w,((hwp.add hwc).sub hwa).add hws,native_all_scale_H2_local (fun s=>?_),?_,fun s=>⟨hj s,hm s⟩⟩
  · exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hj s)).mp (hm s)
  · intro t
    have hc:(fun θ=>wc (t,θ))=ᵐ[angularVolume]
        (nativeLowCauchyCurve ht (nativeLowCauchyCoordinateCLM
          (nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n)))) t:S→ℝ):=by
      dsimp only [wc,q]
      unfold nativeSupportedLowCauchyCoefficients
      exact nativeLowCauchyCurve_ae ht (nativeLowCauchyCoordinateCLM
          (nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n)))) t
    exact angular_add_rep (angular_sub_rep (angular_add_rep (hpa t) hc) (haa t)) (hsa t)

theorem exists_nativeSupportedOuter_same_field_decay (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
      (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐs:ℝ ∂volume,s<b→F s=0)→
      ∃w:ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ:Set E) ∧
        (∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ)) ∧
        (∀s:ℝ,NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w) ∧
        (∀t:ℝ,t≤0→‖Real.exp (t/2) • nativeSupportedOuterCurve b ht F d n σ t‖≤
          C*(‖(F,(d,n))‖+‖σ‖)*Real.exp (t/2)) ∧
        Tendsto (fun t:ℝ=>Real.exp (t/2) • nativeSupportedOuterCurve b ht F d n σ t) atBot (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩:=exists_nativeSupportedOuterCurve_halfLine_bound b ht
  refine ⟨C,hC,fun F d n σ hσ hF=>?_⟩
  obtain ⟨w,hw,hl,ha,hj⟩:=exists_nativeSupportedOuter_same_curve_all_scale b ht F d n σ hσ
  refine ⟨w,hw,hl,ha,fun s=>(hj s).1,?_,nativeSupportedOuterCurve_physical_decay b ht F d n σ hF⟩
  intro t ht'
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (hbound F d n σ hF t ht') (Real.exp_pos _).le).trans_eq (mul_comm _ _)

#print axioms exists_nativeSupportedOuter_same_curve_all_scale
#print axioms exists_nativeSupportedOuter_same_field_decay
end Yamabe3.Analysis.SpherePolar
