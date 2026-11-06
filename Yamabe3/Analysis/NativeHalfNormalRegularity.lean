import Yamabe3.Analysis.NativeParticularNormalRegularity

/-! The same zero-high-value half-end field has its actual normal trace
in the half-order spectral space required by the coupled boundary inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)

theorem nativePoissonPhysicalEntranceNormal_half_bound (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    NativeAngularSpectralRegular (1/2) (nativePoissonPhysicalEntranceNormal P b) ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (nativePoissonPhysicalEntranceNormal P b) i)≤
        2*(P.derivativeBound^2+1/4)*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have hb' : NativeAngularSpectralRegular ((1/2:ℝ)+1) (angularEmbedding b) := by convert hb using 1 <;> norm_num
  obtain ⟨hd,hdb⟩ := P.dtn_spectral_regular b (1/2) hb'
  have he : P.curve b 0=nativeHighProjection (angularEmbedding b) := by
    rw [NativeHighPotential.curve,nativeHalfHighPotentialPhysical_zero,nativeHighEnergyProjectionCLM_embedding]
  obtain ⟨hu,hub⟩ := nativeAngular_three_halves_to_half (angularEmbedding b) hb
  obtain ⟨hh,hhb⟩ := nativeAngularSpectralRegular_high hu
  obtain ⟨hv,hvb⟩ := nativeAngularSpectralRegular_smul hh (1/2)
  obtain ⟨hs,hsb⟩ := nativeAngularSpectralRegular_sub hd hv
  unfold nativePoissonPhysicalEntranceNormal
  rw [he]
  refine ⟨hs,?_⟩
  norm_num at hdb hvb
  have hp0 : 0≤P.derivativeBound^2 := sq_nonneg _
  nlinarith only [hdb,hub,hhb,hvb,hsb]

variable (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeL2HalfNormalAngularCLM : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  nativeTraceAngularCLM.comp (nativeL2HalfNormalTraceCLM P hp)

theorem nativeL2HalfNormalAngular_difference
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    nativeL2HalfNormalAngularCLM P hp F=nativeL2ParticularNormalAngularCLM P hp F-
      nativePoissonPhysicalEntranceNormal P (nativeL2HalfEntrance P hp F) := by
  change nativeTraceAngularCLM (nativeL2HalfNormalTraceCLM P hp F)=_
  rw [nativeL2HalfNormalTrace_difference,map_sub,nativeTraceAngular_left_inverse]
  rfl

theorem nativeL2HalfNormalAngular_half_bound
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    NativeAngularSpectralRegular (1/2) (nativeL2HalfNormalAngularCLM P hp F) ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (nativeL2HalfNormalAngularCLM P hp F) i)≤
        (3+4*P.derivativeBound^2)*(50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2*‖F‖^2 := by
  obtain ⟨hpar,hparb⟩ := nativeL2ParticularNormalAngular_half_bound P hp F
  have he := nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F
  obtain ⟨hpois,hpoisb⟩ := nativePoissonPhysicalEntranceNormal_half_bound P (nativeL2HalfEntrance P hp F) he.2.1
  obtain ⟨hsub,hsubb⟩ := nativeAngularSpectralRegular_sub hpar hpois
  rw [nativeL2HalfNormalAngular_difference]
  refine ⟨hsub,?_⟩
  have hm := mul_le_mul_of_nonneg_left he.2.2.1
    (by positivity : 0≤2*(P.derivativeBound^2+1/4))
  change 2*(P.derivativeBound^2+1/4)*(∑' i,nativeAngularWeightedSquare (3/2)
    (angularEmbedding (nativeL2HalfEntrance P hp F)) i)≤_ at hm
  nlinarith only [hparb,hpoisb,hsubb,hm]

#print axioms nativePoissonPhysicalEntranceNormal_half_bound
#print axioms nativeL2HalfNormalAngular_difference
#print axioms nativeL2HalfNormalAngular_half_bound
end Yamabe3.Analysis.SpherePolar
