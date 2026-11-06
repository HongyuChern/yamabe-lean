import Yamabe3.Analysis.NativeFullTraceRegularity
import Yamabe3.Analysis.NativeC2C1HighCauchy

/-! The high correction of the actual full-source interior field.
The same source produces its true radial trace, the coupled inverse
witness, and one new H2 collar jet. Low value and normal data are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (B P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

def nativeFullSourceBoundarySigma (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : AngularH1 :=
  nativeHighCoupledDtNInverse B P (-nativeFullL2NormalAngularCLM P hp v hv hb F)

theorem nativeFullSourceBoundarySigma_high (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeHighEnergyProjectionCLM (nativeFullSourceBoundarySigma B P hp v hv hb F)=
      nativeFullSourceBoundarySigma B P hp v hv hb F := nativeHighCoupledDtNInverse_high _ _ _

theorem nativeFullSourceBoundarySigma_spectral (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeFullSourceBoundarySigma B P hp v hv hb F)) ∧
      (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeFullSourceBoundarySigma B P hp v hv hb F)) i) ≤
        4*(∑'i,nativeAngularWeightedSquare (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb F) i) := by
  have hn := (nativeFullL2NormalAngular_half_bound P hp v hv hb F).1
  have hneg := nativeAngularSpectralRegular_smul hn (-1)
  simp only [neg_one_smul] at hneg
  have h := nativeHighCoupled_inverse_spectral_regular B P (1/2)
    (-nativeFullL2NormalAngularCLM P hp v hv hb F) hneg.1
  norm_num at hneg
  rw [hneg.2] at h
  convert h using 1 <;> norm_num [nativeFullSourceBoundarySigma]

theorem nativeFullSourceBoundarySigma_equation (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    B.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F)+
      P.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F)=
        -nativeHighProjection (nativeFullL2NormalAngularCLM P hp v hv hb F) := by
  change (B.dtn+P.dtn) (nativeHighCoupledDtNInverse B P (-nativeFullL2NormalAngularCLM P hp v hv hb F))=_
  rw [nativeHighCoupledDtNInverse_right,map_neg]

def nativeFullSourceMatchedInteriorJet (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : nativeCollarJetClosure :=
  nativeFullL2AllScaleJetCLM P hp v hv hb 0 F+
    nativePoissonCollarJet P (nativeFullSourceBoundarySigma B P hp v hv hb F)
      (nativeFullSourceBoundarySigma_spectral B P hp v hv hb F).1

theorem nativeFullSourceMatchedInterior_traces (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeFullSourceMatchedInteriorJet B P hp v hv hb F))=
      nativeLowL2AngularCLM v hv hb F 0+angularEmbedding (nativeFullSourceBoundarySigma B P hp v hv hb F) ∧
    nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeFullSourceMatchedInteriorJet B P hp v hv hb F))=
      nativeFullL2NormalAngularCLM P hp v hv hb F+
        P.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F)-
          (1/2:ℝ) • angularEmbedding (nativeFullSourceBoundarySigma B P hp v hv hb F) := by
  constructor
  · unfold nativeFullSourceMatchedInteriorJet
    rw [map_add,map_add,nativeFullL2_value_trace,nativePoissonCollarJet_value_trace,
      nativeTraceAngular_left_inverse,nativeTraceAngular_left_inverse,
      P.curve_zero _ (nativeFullSourceBoundarySigma_high B P hp v hv hb F)]
  · unfold nativeFullSourceMatchedInteriorJet
    rw [map_add,map_add,nativePoissonCollarJet_normal_trace,nativeTraceAngular_left_inverse]
    change nativeFullL2NormalAngularCLM P hp v hv hb F+
      (P.dtn (nativeFullSourceBoundarySigma B P hp v hv hb F)-(1/2:ℝ) •
        P.curve (nativeFullSourceBoundarySigma B P hp v hv hb F) 0)=_
    rw [P.curve_zero _ (nativeFullSourceBoundarySigma_high B P hp v hv hb F)]
    abel

#print axioms nativeFullSourceBoundarySigma_spectral
#print axioms nativeFullSourceBoundarySigma_equation
#print axioms nativeFullSourceMatchedInterior_traces
end Yamabe3.Analysis.SpherePolar
