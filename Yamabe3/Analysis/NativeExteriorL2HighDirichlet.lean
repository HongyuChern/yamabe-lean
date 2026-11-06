import Yamabe3.Analysis.NativeBubbleExteriorL2Potential
import Yamabe3.Analysis.NativeExteriorBoundaryOperators
import Yamabe3.Analysis.NativeExteriorModelJacobian

/-! Actual exterior zero-value high-mode solution for L2 source data.
The full-line particular field has the same exterior potential, and its
actual entrance is cancelled by the reversed Poisson field. The source
projection and coefficient -8 remain explicit. Far-end estimates are a
separate obligation; this module claims the collar producer and equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable (P B : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeExteriorL2EntranceCorrectionCLM :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeExteriorBoundaryJetCLM B
    (nativeL2EntranceH1CLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp)
    (fun F => (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F).2.1)
    ⟨(50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2,by positivity,
      fun F => (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F).2.2.1⟩

def nativeExteriorL2HighJetCLM :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeL2ParticularJetCLM P hp-nativeExteriorL2EntranceCorrectionCLM P B hp

theorem nativeExteriorL2HighJetCLM_eq (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeExteriorL2HighJetCLM P B hp F=nativeL2ParticularJetCLM P hp F-
      nativePoissonExteriorCollarJet B
        (nativeL2EntranceH1 P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F)
        (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F).2.1 := rfl

theorem nativeExteriorL2HighJet_zero_value (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeCollarValueTraceCLM (nativeExteriorL2HighJetCLM P B hp F)=0 := by
  rw [nativeExteriorL2HighJetCLM_eq,map_sub,nativeL2ParticularJet_value_trace,
    nativePoissonExteriorCollarJet_value_trace]
  have he := (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F).1
  rw [NativeHighPotential.curve,nativeHalfHighPotentialPhysical_zero,
    nativeHighEnergyProjectionCLM_embedding,he]
  exact sub_self _

theorem nativeExteriorL2HighJet_equation
    (hV : P.potential=nativePoissonExteriorPotential B)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential B)
      (nativeExteriorL2HighJetCLM P B hp F).val=
      (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeL2HighPhysicalSourceCLM F) := by
  rw [nativeExteriorL2HighJetCLM_eq,Submodule.coe_sub,map_sub,nativeExteriorModelJacobian_high_zero,sub_zero]
  rw [←hV,nativeExteriorModelJacobianCLM_apply]
  change (-8:ℝ) • nativeNegativeCollarRestrictionCLM
    ((∑j : Fin 3,nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp j j F)+
      nativeCollarPotentialMulCLM P.potential
        (nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hp F))=_
  rw [nativeL2Particular_physical_equation]

omit P B hp in
theorem nativeBubbleExteriorL2High_actual_solver (t₀ : ℝ) :
    ∃T : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure,
      ∀F, nativeCollarValueTraceCLM (T F)=0 ∧
      nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))) (T F).val=
        (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeL2HighPhysicalSourceCLM F) := by
  refine ⟨nativeExteriorL2HighJetCLM (fullBubbleHighPotential t₀) (fullBubbleHighPotential (-t₀))
    (fullBubblePhasePotential_plus_kernel t₀),fun F => ⟨?_,?_⟩⟩
  · exact nativeExteriorL2HighJet_zero_value _ _ _ F
  · exact nativeExteriorL2HighJet_equation _ _ _ (nativeBubbleExteriorPotential_eq_phase t₀).symm F

#print axioms nativeExteriorL2HighJetCLM_eq
#print axioms nativeExteriorL2HighJet_zero_value
#print axioms nativeExteriorL2HighJet_equation
#print axioms nativeBubbleExteriorL2High_actual_solver
end Yamabe3.Analysis.SpherePolar
