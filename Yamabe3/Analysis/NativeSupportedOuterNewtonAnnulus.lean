import Yamabe3.Analysis.NativeSupportedOuterNewtonH4
import Yamabe3.Analysis.WeightedNewtonCollarToAnnulus

/-! The same Newton-rate field is fixed before every far-scale Sobolev estimate. The H2
and H4 conclusions concern that same physical field and its weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

 theorem exists_nativeSupportedOuter_same_field_Newton_H4
    {V W:Set E} (hV:IsOpen V) (hVc:IsCompact (closure V))
    (hVD:closure V⊆nativePoissonEntranceCollar)
    (hW:IsOpen W) (hWc:IsCompact (closure W)) (hWV:closure W⊆V)
    (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃S:ℝ,S≤-(1/2:ℝ) ∧ ∃C:ℝ≥0∞,C≠⊤ ∧
      ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
        (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→
      ∃w:ℝ×SpherePolar.S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ:Set E) ∧
        (∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:SpherePolar.S→ℝ)) ∧
        (∀s:ℝ,NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w) ∧
        ∀s:ℝ,s≤S→MemWkp 4 2 (weightedPhysicalDilation s (cylinderLift w)) W ∧
          ∀k:ℕ,k≤4→iteratedWeakSobolevNorm k 2 (weightedPhysicalDilation s (cylinderLift w)) W≤
            C*ENNReal.ofReal (Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖)) := by
  obtain ⟨S,hS,C,hC,h⟩:=exists_nativeSupportedOuter_Newton_far_H4_bound hV hVc hVD hW hWc hWV b ht
  refine ⟨S,hS,C,hC,fun F d n σ hσ hF=>?_⟩
  obtain ⟨w,hw,hl,ha,hj⟩:=exists_nativeSupportedOuter_same_curve_all_scale b ht F d n σ hσ
  refine ⟨w,hw,hl,ha,fun s=>(hj s).1,fun s hs=>?_⟩
  have hWD:W⊆nativePoissonEntranceCollar:=subset_closure.trans (hWV.trans (subset_closure.trans hVD))
  have hr:((nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1:E→ℝ)=ᵐ[volume.restrict W]
      weightedPhysicalDilation s (cylinderLift w):=
    ae_mono (Measure.restrict_mono hWD le_rfl) (hj s).1
  have hh:=h F d n σ hσ hF s hs
  refine ⟨(MemWkp_congr_ae (by norm_num) hW hr).mp hh.1,fun k hk=>?_⟩
  rw [←wkpNorm_congr_ae (k:=k) (by norm_num) hW hr]
  exact (wkpNorm_mono_order hk _ W).trans hh.2

 theorem exists_nativeSupportedOuter_same_field_Newton_annulus_H4 (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃T:ℝ,T≤-(1/2:ℝ) ∧ ∃C:ℝ≥0∞,C≠⊤ ∧
      ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
        (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ)),
      (∀ᵐt:ℝ ∂volume,t<b→F t=0)→
      ∃w:ℝ×S→ℝ,Measurable w ∧ MemWkpLocally 2 (cylinderLift w) ({0}ᶜ:Set E) ∧
        (∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ)) ∧
        (∀s:ℝ,NativeScaledJetRep (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s) s w) ∧
        ∀s:ℝ,s≤T→MemWkp 4 2 (weightedPhysicalDilation s (cylinderLift w)) halfEndBasicAnnulus ∧
          ∀k:ℕ,k≤4→iteratedWeakSobolevNorm k 2 (weightedPhysicalDilation s (cylinderLift w)) halfEndBasicAnnulus≤
            C*ENNReal.ofReal (Real.exp (5*s/2)*(‖(F,(d,n))‖+‖σ‖)) := by
  let V:=nativePolarTimeWindow (Ioo (-(3/8:ℝ)) (3/8))
  let W:=nativePolarTimeWindow (Ioo (-(1/4:ℝ)) (1/4))
  obtain ⟨T,hT,C₀,hC₀,h⟩:=exists_nativeSupportedOuter_same_field_Newton_H4
    (nativePolarTimeWindow_open (3/8)) (nativePolarTimeWindow_precompact (3/8))
    (nativePolarTimeWindow_nested (by norm_num:(3/8:ℝ)<1/2))
    (nativePolarTimeWindow_open (1/4)) (nativePolarTimeWindow_precompact (1/4))
    (nativePolarTimeWindow_nested (by norm_num:(1/4:ℝ)<3/8)) b ht
  obtain ⟨D,hD,hd⟩:=exists_weighted_Newton_collar_to_annulus_H4_bound
  refine ⟨T-1,by linarith only [hT],D*C₀,by finiteness,fun F d n σ hσ hF=>?_⟩
  obtain ⟨w,hw,hl,ha,hj,hreg⟩:=h F d n σ hσ hF
  refine ⟨w,hw,hl,ha,hj,fun s hs=>?_⟩
  let N:=‖(F,(d,n))‖+‖σ‖
  have hb:∀t:ℝ,t≤T→MemWkp 4 2 (weightedPhysicalDilation t (cylinderLift w)) W ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation t (cylinderLift w)) W≤
        ENNReal.ofReal (Real.exp (5*t/2))*(C₀*ENNReal.ofReal N):=by
    intro t ht'
    have hh:=hreg t ht'
    refine ⟨hh.1,(hh.2 4 (le_refl 4)).trans_eq ?_⟩
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  have hh:=hd (cylinderLift w) (C₀*ENNReal.ofReal N) T hb s hs
  refine ⟨hh.1,fun k hk=>(wkpNorm_mono_order hk _ halfEndBasicAnnulus).trans (hh.2.trans_eq ?_)⟩
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

#print axioms exists_nativeSupportedOuter_same_field_Newton_H4
#print axioms exists_nativeSupportedOuter_same_field_Newton_annulus_H4
end Yamabe3.Analysis.SpherePolar
