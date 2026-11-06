import Yamabe3.Analysis.NativeLowReverseL2PhysicalEquation
import Yamabe3.Analysis.NativeLowReverseL2NormalTrace
import Yamabe3.Analysis.NativeLowReverseL2Decay
import Yamabe3.Analysis.NativeBubbleExteriorL2Potential
import Yamabe3.Analysis.NativeExteriorModelJacobian

/-! A concrete low-mode exterior bubble solver. The profile is obtained
from the literal bubble density, so its equation is not conditional on
an unidentified coefficient. The same source, coefficient field, collar
jet, real traces and exterior decay are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeBubbleReverseProfile (t₀ t : ℝ) : ℝ := Real.sqrt (Real.sqrt (fullBubbleDensity (t₀-t)))

theorem nativeBubbleReverseProfile_continuous (t₀ : ℝ) : Continuous (nativeBubbleReverseProfile t₀) :=
  (Real.continuous_sqrt.comp Real.continuous_sqrt).comp
    (fullBubbleDensity_continuous.comp (continuous_const.sub continuous_id))

theorem nativeBubbleReverseProfile_bounds (t₀ t : ℝ) :
    0≤nativeBubbleReverseProfile t₀ t ∧ nativeBubbleReverseProfile t₀ t≤1 :=
  ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr (fullBubbleDensity_bounds _).2)⟩

theorem nativeBubbleReverseProfile_fourth (t₀ t : ℝ) :
    nativeBubbleReverseProfile t₀ t^4=fullBubbleDensity (t₀-t) := by
  unfold nativeBubbleReverseProfile
  rw [show Real.sqrt (Real.sqrt (fullBubbleDensity (t₀-t)))^4=
    (Real.sqrt (Real.sqrt (fullBubbleDensity (t₀-t)))^2)^2 by ring,
    Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt (fullBubbleDensity_bounds _).1]

theorem nativeBubbleReversePotential_eq (t₀ : ℝ) :
    nativeLowReversePotential (nativeBubbleReverseProfile t₀)
      (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀)=
      nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)) := by
  rw [nativeBubbleExteriorPotential_eq_phase]
  ext t
  change (15/4:ℝ)*nativeBubbleReverseProfile t₀ (-t+0)^4=(15/4)*fullBubbleDensity (t+t₀)
  rw [add_zero,nativeBubbleReverseProfile_fourth,show t₀-(-t)=t+t₀ by ring]

def nativeBubbleLowReverseJetCLM (t₀ : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] nativeCollarJetClosure :=
  nativeLowReverseL2JetCLM (nativeBubbleReverseProfile t₀)
    (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀)

theorem nativeBubbleLowReverseJet_equation (t₀ : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeExteriorModelJacobianCLM (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))
      (nativeBubbleLowReverseJetCLM t₀ F).val=
        (-8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeLowReverseL2SourceCLM F) := by
  rw [←nativeBubbleReversePotential_eq,nativeExteriorModelJacobianCLM_apply]
  change (-8:ℝ) • nativeNegativeCollarRestrictionCLM
    ((∑j : Fin 3,(nativeLowReverseL2RawJetCLM (nativeBubbleReverseProfile t₀)
      (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀) F).2.2 j j)+
      nativeCollarPotentialMulCLM _ (nativeLowReverseL2RawJetCLM (nativeBubbleReverseProfile t₀)
        (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀) F).1)=_
  rw [nativeLowReverseL2_physical_equation]

theorem nativeBubbleLowReverseJet_traces (t₀ : ℝ) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeCollarValueTraceCLM (nativeBubbleLowReverseJetCLM t₀ F)=
      nativeAngularTraceCLM (nativeLowL2AngularCLM (nativeBubbleReverseProfile t₀)
        (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀) F 0) ∧
    nativeCollarNormalTraceCLM (nativeBubbleLowReverseJetCLM t₀ F)=
      nativeAngularTraceCLM (nativeLowReverseL2NormalAngularCLM (nativeBubbleReverseProfile t₀)
        (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀) F) :=
  ⟨nativeLowReverseL2Jet_value_trace _ _ _ F,nativeLowReverseL2Jet_normal_trace _ _ _ F⟩

theorem nativeBubbleLowReverseCoefficient_decay (t₀ : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (i : AngularIndex) :
    let q := nativeLowReverseL2Coefficient (nativeBubbleReverseProfile t₀)
      (nativeBubbleReverseProfile_continuous t₀) (nativeBubbleReverseProfile_bounds t₀) F i
    Tendsto q atBot (𝓝 0) ∧ Tendsto (deriv q) atBot (𝓝 0) :=
  nativeLowReverseL2Coefficient_bot _ _ _ F i

#print axioms nativeBubbleReverseProfile_continuous
#print axioms nativeBubbleReverseProfile_bounds
#print axioms nativeBubbleReverseProfile_fourth
#print axioms nativeBubbleReversePotential_eq
#print axioms nativeBubbleLowReverseJet_equation
#print axioms nativeBubbleLowReverseJet_traces
#print axioms nativeBubbleLowReverseCoefficient_decay
end Yamabe3.Analysis.SpherePolar
