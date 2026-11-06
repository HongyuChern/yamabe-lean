import Yamabe3.Analysis.NativeExteriorL2HighDirichlet
import Yamabe3.Analysis.NativeHalfNormalRegularity

/-! The actual exterior inhomogeneous field supplies its normal datum
in the half-order scale used by the two-sided high boundary inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativePoissonExteriorPhysicalEntranceNormal_half_bound (B : NativeHighPotential)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    NativeAngularSpectralRegular (1/2) (nativePoissonExteriorPhysicalEntranceNormal B b) ∧
      (∑'i,nativeAngularWeightedSquare (1/2) (nativePoissonExteriorPhysicalEntranceNormal B b) i)≤
        2*(B.derivativeBound^2+1/4)*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have hb' : NativeAngularSpectralRegular ((1/2:ℝ)+1) (angularEmbedding b) := by convert hb using 1 <;> norm_num
  obtain ⟨hd,hdb⟩ := B.dtn_spectral_regular b (1/2) hb'
  obtain ⟨hnd,hndb⟩ := nativeAngularSpectralRegular_smul hd (-1)
  simp only [neg_one_smul,neg_sq,one_pow,one_mul] at hnd hndb
  have he : B.curve b 0=nativeHighProjection (angularEmbedding b) := by
    rw [NativeHighPotential.curve,nativeHalfHighPotentialPhysical_zero,nativeHighEnergyProjectionCLM_embedding]
  obtain ⟨hu,hub⟩ := nativeAngular_three_halves_to_half (angularEmbedding b) hb
  obtain ⟨hh,hhb⟩ := nativeAngularSpectralRegular_high hu
  obtain ⟨hv,hvb⟩ := nativeAngularSpectralRegular_smul hh (1/2)
  obtain ⟨hs,hsb⟩ := nativeAngularSpectralRegular_sub hnd hv
  unfold nativePoissonExteriorPhysicalEntranceNormal
  rw [he]
  refine ⟨hs,?_⟩
  norm_num at hdb hvb
  have hp0 : 0≤B.derivativeBound^2 := sq_nonneg _
  nlinarith only [hndb,hdb,hub,hhb,hvb,hsb]

variable (P B : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeExteriorL2HighNormalAngularCLM :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  nativeTraceAngularCLM.comp (nativeCollarNormalTraceCLM.comp (nativeExteriorL2HighJetCLM P B hp))

theorem nativeExteriorL2HighNormalAngular_difference
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeExteriorL2HighNormalAngularCLM P B hp F=nativeL2ParticularNormalAngularCLM P hp F-
      nativePoissonExteriorPhysicalEntranceNormal B
        (nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F) := by
  change nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeExteriorL2HighJetCLM P B hp F))=_
  rw [nativeExteriorL2HighJetCLM_eq,map_sub,map_sub,nativePoissonExteriorCollarJet_normal_trace,
    nativeTraceAngular_left_inverse]
  rfl

theorem nativeExteriorL2HighNormalAngular_half_bound
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    NativeAngularSpectralRegular (1/2) (nativeExteriorL2HighNormalAngularCLM P B hp F) ∧
      (∑'i,nativeAngularWeightedSquare (1/2) (nativeExteriorL2HighNormalAngularCLM P B hp F) i)≤
        (3+4*B.derivativeBound^2)*(50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2*‖F‖^2 := by
  obtain ⟨hpar,hparb⟩ := nativeL2ParticularNormalAngular_half_bound P hp F
  have he := nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F
  obtain ⟨hpois,hpoisb⟩ := nativePoissonExteriorPhysicalEntranceNormal_half_bound B _ he.2.1
  obtain ⟨hsub,hsubb⟩ := nativeAngularSpectralRegular_sub hpar hpois
  rw [nativeExteriorL2HighNormalAngular_difference]
  refine ⟨hsub,?_⟩
  have hm := mul_le_mul_of_nonneg_left he.2.2.1
    (by positivity : 0≤2*(B.derivativeBound^2+1/4))
  nlinarith only [hparb,hpoisb,hsubb,hm]

#print axioms nativePoissonExteriorPhysicalEntranceNormal_half_bound
#print axioms nativeExteriorL2HighNormalAngular_difference
#print axioms nativeExteriorL2HighNormalAngular_half_bound
end Yamabe3.Analysis.SpherePolar
