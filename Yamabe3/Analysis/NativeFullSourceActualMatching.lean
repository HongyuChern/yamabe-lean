import Yamabe3.Analysis.NativeFullSourceLowMatching
import Yamabe3.Analysis.NativeBubbleLowCollar

/-! The same full L2 source now produces two genuine H2 collar jets with
both actual traces matched. The finite low compensating source remains
explicit. General geometric perturbation is not assumed or asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

private theorem traceAngular_injective : Function.Injective nativeTraceAngularCLM := by
  intro x y h
  rw [←nativeTraceAngular_right_inverse x,←nativeTraceAngular_right_inverse y,h]

variable (B P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

theorem nativeFullSource_actual_collar_matching
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (t₀ : ℝ) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i))
    (hvalue : bubbleLowAngularCurve q t₀=nativeLowL2AngularCLM v hv hb F 0)
    (hderiv : deriv (bubbleLowAngularCurve q) t₀=
      -nativeLowProjection (nativeFullL2NormalAngularCLM P hp v hv hb F)-
        (1/2:ℝ) • nativeLowL2AngularCLM v hv hb F 0) :
    let σ := nativeFullSourceBoundarySigma B P hp v hv hb F
    let K := nativeBubbleLowCollarJet t₀ q hq+
      nativePoissonExteriorCollarJet B σ (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1
    let J := nativeFullSourceMatchedInteriorJet B P hp v hv hb F
    nativeCollarValueTraceCLM K=nativeCollarValueTraceCLM J ∧
      nativeCollarNormalTraceCLM K=nativeCollarNormalTraceCLM J := by
  dsimp only
  have hs := nativeFullSourceBoundarySigma_high B P hp v hv hb F
  have hc := nativeFullSourceBoundarySigma_equation B P hp v hv hb F
  have hdec := nativeHighProjection_add_low (nativeFullL2NormalAngularCLM P hp v hv hb F)
  constructor
  · apply traceAngular_injective
    rw [map_add,map_add,nativeBubbleLowCollarJet_value_trace,nativePoissonExteriorCollarJet_value_trace,
      nativeTraceAngular_left_inverse,nativeTraceAngular_left_inverse,hvalue,B.curve_zero _ hs]
    exact (nativeFullSourceMatchedInterior_traces B P hp v hv hb F).1.symm
  · apply traceAngular_injective
    rw [map_add,map_add,nativeBubbleLowCollarJet_normal_trace,nativePoissonExteriorCollarJet_normal_trace,
      nativeTraceAngular_left_inverse,nativeTraceAngular_left_inverse,hderiv,hvalue]
    unfold nativePoissonExteriorPhysicalEntranceNormal
    rw [B.curve_zero _ hs,(nativeFullSourceMatchedInterior_traces B P hp v hv hb F).2]
    have hc' : nativeLowProjection (nativeFullL2NormalAngularCLM P hp v hv hb F)-
        B.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F)=
      nativeFullL2NormalAngularCLM P hp v hv hb F+
        P.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F) := by
      calc
        _=nativeLowProjection (nativeFullL2NormalAngularCLM P hp v hv hb F)-
          (B.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F)+
            P.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F))+
          P.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F) := by abel
        _=_ := by rw [hc,sub_neg_eq_add,add_comm (nativeLowProjection _) (nativeHighProjection _),hdec]
    calc
      _=(nativeLowProjection (nativeFullL2NormalAngularCLM P hp v hv hb F)-
          B.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F))-
          (1/2:ℝ) • angularEmbedding (nativeFullSourceBoundarySigma B P hp v hv hb F) := by abel
      _=_ := by rw [hc']

theorem exists_nativeFullSource_actual_H2_collar_matching
    {t₀ : ℝ} (ht : 0<t₀) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    let B := fullBubbleHighPotential (-t₀)
    let σ := nativeFullSourceBoundarySigma B P hp v hv hb F
    let J := nativeFullSourceMatchedInteriorJet B P hp v hv hb F
    let d := nativeLowL2AngularCLM v hv hb F 0
    let N := nativeFullL2NormalAngularCLM P hp v hv hb F
    ∃ (c : AngularIndex → ℝ) (q : AngularIndex → ℝ → ℝ)
      (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)),
      (∀i∈nativeLowIndexFinset,
        c i=bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) d)
          (inner ℝ (angularBasis i) (-N-(1/2:ℝ) • d)) 0 ∧
        (∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t= -c i*bubbleCompensation i t) ∧
        Tendsto (q i) atBot (𝓝 0) ∧ Tendsto (deriv (q i)) atBot (𝓝 0)) ∧
      let K := nativeBubbleLowCollarJet t₀ q hq+
        nativePoissonExteriorCollarJet B σ (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1
      MemWkp 2 2 (J.val.1 : E → ℝ) nativePoissonEntranceCollar ∧
      MemWkp 2 2 (K.val.1 : E → ℝ) nativePoissonEntranceCollar ∧
      nativeCollarValueTraceCLM K=nativeCollarValueTraceCLM J ∧
      nativeCollarNormalTraceCLM K=nativeCollarNormalTraceCLM J := by
  dsimp only
  let d := nativeLowL2AngularCLM v hv hb F 0
  let N := nativeFullL2NormalAngularCLM P hp v hv hb F
  let n := -N-(1/2:ℝ) • d
  have hd : nativeLowProjection d=d := nativeLowL2_entrance_is_low v hv hb F
  obtain ⟨c,q,hq,hqv,hqn⟩ := exists_actual_angular_low_cauchy_solver (0 : ℝ →ᵇ AngularL2) ht d n
  let hC := fun i hi => (hq i hi).2.1
  have hvq : bubbleLowAngularCurve q t₀=d := hqv.trans hd
  have hnq : deriv (bubbleLowAngularCurve q) t₀= -nativeLowProjection N-(1/2:ℝ) • d := by
    rw [hqn.deriv]
    dsimp only [n]
    rw [map_sub,map_neg,map_smul,hd]
  have hm := nativeFullSource_actual_collar_matching (fullBubbleHighPotential (-t₀)) P hp v hv hb F t₀ q hC hvq hnq
  refine ⟨c,q,hC,?_,nativeCollarJetClosure_memH2 _,nativeCollarJetClosure_memH2 _,hm⟩
  intro i hi
  have hzero (t : ℝ) : (0 : ℝ →ᵇ AngularL2) t=0 := rfl
  refine ⟨?_,?_,(hq i hi).2.2.2.2.2⟩
  · simpa only [bubbleLowSourceMoment,bubbleSourceCoordinate_apply,hzero,inner_zero_right,mul_zero,integral_zero] using (hq i hi).1
  · intro t
    simpa only [hzero,inner_zero_right,mul_zero,zero_add,neg_mul] using (hq i hi).2.2.1 t

#print axioms nativeFullSource_actual_collar_matching
#print axioms exists_nativeFullSource_actual_H2_collar_matching
end Yamabe3.Analysis.SpherePolar
