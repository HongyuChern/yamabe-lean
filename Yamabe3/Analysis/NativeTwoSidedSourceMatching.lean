import Yamabe3.Analysis.NativeTwoSidedSourceJets
import Yamabe3.Analysis.NativeMatchedWeakBoundaryAssembly

/-! Both actual Cauchy traces of the same two-sided inhomogeneous pair
match. Consequently the actual piecewise field is H1 and satisfies the
native weak gluing identity. Geometric equation residuals are still
separate explicit terms; this module does not discard them. -/
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

theorem nativeTwoSidedInterior_traces (t₀ : ℝ) (X : NativeTwoSidedSource) :
    let σ := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
    let J := nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X
    nativeTraceAngularCLM (nativeCollarValueTraceCLM J)=nativeLowL2AngularCLM v hv hb X.1 0+angularEmbedding σ ∧
    nativeTraceAngularCLM (nativeCollarNormalTraceCLM J)=nativeFullL2NormalAngularCLM P hp v hv hb X.1+
      P.dtn σ-(1/2:ℝ) • angularEmbedding σ := by
  dsimp only
  rw [nativeTwoSidedInteriorJetCLM_eq]
  have hs := nativeTwoSidedSourceSigma_high P hp v hv hb t₀ X
  constructor
  · rw [map_add,map_add,nativeFullL2_value_trace,nativePoissonCollarJet_value_trace,
      nativeTraceAngular_left_inverse,nativeTraceAngular_left_inverse,P.curve_zero _ hs]
  · rw [map_add,map_add,nativePoissonCollarJet_normal_trace,nativeTraceAngular_left_inverse]
    change nativeFullL2NormalAngularCLM P hp v hv hb X.1+
      (P.dtn (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X)-(1/2:ℝ) •
        P.curve (nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X) 0)=_
    rw [P.curve_zero _ hs]
    abel

theorem nativeTwoSidedExterior_traces {t₀ : ℝ} (ht : 0<t₀) (X : NativeTwoSidedSource) :
    let B := fullBubbleHighPotential (-t₀)
    let σ := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
    let K := nativeTwoSidedExteriorJetCLM P hp v hv hb ht X
    nativeTraceAngularCLM (nativeCollarValueTraceCLM K)=nativeLowL2AngularCLM v hv hb X.1 0+angularEmbedding σ ∧
    nativeTraceAngularCLM (nativeCollarNormalTraceCLM K)=
      nativeLowProjection (nativeFullL2NormalAngularCLM P hp v hv hb X.1)+nativeBubbleExteriorHighNormalCLM t₀ X.2-
        B.dtn σ-(1/2:ℝ) • angularEmbedding σ := by
  dsimp only
  rw [nativeTwoSidedExteriorJetCLM_eq]
  let σ := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
  let B := fullBubbleHighPotential (-t₀)
  have hs := nativeTwoSidedSourceSigma_high P hp v hv hb t₀ X
  have hsrc := nativeBubbleExteriorInhomogeneousJet_traces ht X.2
    (nativeLowL2AngularCLM v hv hb X.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.1)
  constructor
  · rw [map_add,map_add,hsrc.1,nativePoissonExteriorCollarJet_value_trace,
      nativeTraceAngular_left_inverse,nativeTraceAngular_left_inverse,B.curve_zero _ hs,
      nativeLowL2_entrance_is_low]
  · rw [map_add,map_add,hsrc.2,nativePoissonExteriorCollarJet_normal_trace,
      nativeTraceAngular_left_inverse,nativeTraceAngular_left_inverse]
    change nativeLowProjection (nativeFullL2NormalAngularCLM P hp v hv hb X.1)+nativeBubbleExteriorHighNormalCLM t₀ X.2+
      (-B.dtn σ-(1/2:ℝ) • B.curve σ 0)=_
    rw [B.curve_zero _ hs]
    abel

private theorem traceAngular_injective : Function.Injective nativeTraceAngularCLM := by
  intro x y h
  rw [←nativeTraceAngular_right_inverse x,←nativeTraceAngular_right_inverse y,h]

theorem nativeTwoSidedSource_actual_matching {t₀ : ℝ} (ht : 0<t₀) (X : NativeTwoSidedSource) :
    nativeCollarValueTraceCLM (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X)=
      nativeCollarValueTraceCLM (nativeTwoSidedExteriorJetCLM P hp v hv hb ht X) ∧
    nativeCollarNormalTraceCLM (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X)=
      nativeCollarNormalTraceCLM (nativeTwoSidedExteriorJetCLM P hp v hv hb ht X) := by
  have hi := nativeTwoSidedInterior_traces P hp v hv hb t₀ X
  have he := nativeTwoSidedExterior_traces P hp v hv hb ht X
  constructor
  · exact traceAngular_injective (hi.1.trans he.1.symm)
  · apply traceAngular_injective
    rw [hi.2,he.2]
    let σ := nativeTwoSidedSourceSigmaCLM P hp v hv hb t₀ X
    let B := fullBubbleHighPotential (-t₀)
    let N := nativeFullL2NormalAngularCLM P hp v hv hb X.1
    let E := nativeBubbleExteriorHighNormalCLM t₀ X.2
    have hc : B.dtn σ+P.dtn σ=E-nativeHighProjection N :=
      nativeTwoSidedSourceSigma_equation P hp v hv hb t₀ X
    have hn := nativeHighProjection_add_low N
    have h : N+P.dtn σ=nativeLowProjection N+E-B.dtn σ := by
      calc
        _=(nativeHighProjection N+nativeLowProjection N)+P.dtn σ := congrArg (fun a : AngularL2 => a+P.dtn σ) hn.symm
        _=nativeLowProjection N+(B.dtn σ+P.dtn σ+nativeHighProjection N)-B.dtn σ := by abel
        _=_ := by rw [hc];abel
    exact congrArg (fun a : AngularL2 => a-(1/2:ℝ) • angularEmbedding σ) h

theorem nativeTwoSidedSource_actual_weak_gluing {t₀ : ℝ} (ht : 0<t₀) (X : NativeTwoSidedSource) :
    NativeCollarWeakGluing (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀ X)
      (nativeTwoSidedExteriorJetCLM P hp v hv hb ht X) := by
  have h := nativeTwoSidedSource_actual_matching P hp v hv hb ht X
  exact nativeCollarWeakGluing_of_trace_equal _ _ h.1 h.2

#print axioms nativeTwoSidedInterior_traces
#print axioms nativeTwoSidedExterior_traces
#print axioms nativeTwoSidedSource_actual_matching
#print axioms nativeTwoSidedSource_actual_weak_gluing
end Yamabe3.Analysis.SpherePolar
