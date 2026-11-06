import Yamabe3.Analysis.NativeBubbleExteriorInhomogeneous

/-! The actual exterior nonhomogeneous normal trace has no low angular
component. This is proved from the finite physical traces and source
density; it is not inferred from a module or operator name. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem high_idem (f : AngularL2) : nativeHighProjection (nativeHighProjection f)=nativeHighProjection f := by
  classical
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeHighProjection,nativeAngularProjection_coefficient]
  split_ifs <;> rfl

theorem nativeL2ParticularNormalAngular_high (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeHighProjection (nativeL2ParticularNormalAngularCLM P hp F)=nativeL2ParticularNormalAngularCLM P hp F := by
  have hc := isClosed_eq
    (nativeHighProjection.continuous.comp (nativeL2ParticularNormalAngularCLM P hp).continuous)
    (nativeL2ParticularNormalAngularCLM P hp).continuous
  refine (continuousL2SourceInclusion_dense AngularSpectralSpace).induction_on F hc ?_
  intro H
  have he : nativeL2ParticularNormalAngularCLM P hp (continuousL2SourceInclusion _ H)=
      nativeContinuousParticularNormal P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound H.val := by
    change nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeL2ParticularJetCLM P hp (continuousL2SourceInclusion _ H)))=_
    rw [nativeL2ParticularJet_normal_trace_continuous,nativeTraceAngular_left_inverse]
  rw [he]
  exact high_idem _

theorem nativePoissonExteriorPhysicalEntranceNormal_high (B : NativeHighPotential) (b : AngularH1) :
    nativeHighProjection (nativePoissonExteriorPhysicalEntranceNormal B b)=nativePoissonExteriorPhysicalEntranceNormal B b := by
  unfold nativePoissonExteriorPhysicalEntranceNormal
  rw [map_sub,map_neg,map_smul,B.high]
  have he : B.curve b 0=nativeHighProjection (angularEmbedding b) := by
    rw [NativeHighPotential.curve,nativeHalfHighPotentialPhysical_zero,nativeHighEnergyProjectionCLM_embedding]
  rw [he,high_idem]

theorem nativeExteriorL2HighNormalAngular_high (P B : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeHighProjection (nativeExteriorL2HighNormalAngularCLM P B hp F)=nativeExteriorL2HighNormalAngularCLM P B hp F := by
  rw [nativeExteriorL2HighNormalAngular_difference,map_sub,nativeL2ParticularNormalAngular_high,
    nativePoissonExteriorPhysicalEntranceNormal_high]

#print axioms nativeL2ParticularNormalAngular_high
#print axioms nativePoissonExteriorPhysicalEntranceNormal_high
#print axioms nativeExteriorL2HighNormalAngular_high
end Yamabe3.Analysis.SpherePolar
