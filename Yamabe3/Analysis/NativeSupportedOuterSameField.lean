import Yamabe3.Analysis.NativeSupportedOuterAllScale

/-! One joint representative for the actual corrected exterior field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem exists_nativeSupportedOuter_same_field_all_scale (b : ℝ) {τ : ℝ} (ht : 0<τ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
    (σ : AngularH1) (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ : Set E) ∧
      ∀s : ℝ,NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w ∧
        MemWkp 2 2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1 nativePoissonEntranceCollar := by
  obtain ⟨wp,hwp,_,hjp⟩ := nativeBubbleFullSupported_same_field τ b F
  let P := fullBubbleHighPotential τ
  let B := fullBubbleHighPotential (-τ)
  let a := nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ) F
  let ha := (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ) F).2.1
  obtain ⟨wa,hwa,_,_,hja⟩ := exists_nativeExteriorPoisson_same_field_localH2 B a ha
  obtain ⟨ws,hws,_,_,hjs⟩ := exists_nativeExteriorPoisson_same_field_localH2 B σ hσ
  let q := nativeSupportedLowCauchyCoefficients b ht F d n
  let hq := nativeSupportedLowCauchyCoefficients_C2 b ht F d n
  let wc := finiteAngular nativeLowIndexFinset q
  have hwc := (nativeFiniteAngular_continuous nativeLowIndexFinset q hq).measurable
  let w := fun z => (wp z+wc z)-wa z+ws z
  have hj (s : ℝ) : NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w := by
    have hp : NativeScaledJetRep (nativeSupportedParticularJet τ b s F) s wp := hjp s
    have hc : NativeScaledJetRep (nativeSupportedLowCauchyAllScaleJet b ht F d n s) s wc := by
      change ((nativeFiniteAllScaleJet nativeLowIndexFinset q hq s).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*cylinderLift (finiteAngular nativeLowIndexFinset q) (Real.exp (-s) • x))
      simpa only [finitePhysical_eq_lift] using nativeFiniteAllScaleJet_same_field nativeLowIndexFinset q hq s
    exact ((hp.add hc).sub (hja s).1).add (hjs s).1
  have hm (s : ℝ) := nativeCollarJetClosure_memH2 (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s)
  refine ⟨w,((hwp.add hwc).sub hwa).add hws,native_all_scale_H2_local (fun s => ?_),fun s => ⟨hj s,hm s⟩⟩
  exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hj s)).mp (hm s)

#print axioms exists_nativeSupportedOuter_same_field_all_scale
end Yamabe3.Analysis.SpherePolar
