import Yamabe3.Analysis.SpectralL2PotentialFarEnd
import Yamabe3.Analysis.NativeBubbleExteriorL2Potential
import Yamabe3.Analysis.NativeL2ParticularAllSourceIdentity

/-! Actual negative-time decay of the same canonical bubble particular
field. The full L2 inverse is bootstrapped before conjugation, and the
high angular projection and angular isometry remain explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem fullBubblePhasePotential_left_exp_bound (τ t : ℝ) :
    |fullBubblePhasePotential τ t|≤(15*Real.exp (2*τ))*Real.exp (2*t) := by
  have he := Real.exp_pos (2*(t+τ))
  have hd : 0<(1+Real.exp (2*(t+τ)))^2 := by positivity
  have h : fullBubbleDensity (t+τ)≤4*Real.exp (2*(t+τ)) := by
    unfold fullBubbleDensity
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (Real.exp (2*(t+τ))),mul_nonneg he.le (sq_nonneg (Real.exp (2*(t+τ))))]
  change |(15/4:ℝ)*fullBubbleDensity (t+τ)|≤_
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (fullBubbleDensity_bounds _).1)]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤15/4)).trans_eq
  rw [show 2*(t+τ)=2*t+2*τ by ring,Real.exp_add]
  ring

theorem exists_nativeBubbleParticular_far_end_bound (τ b : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀F : Lp AngularSpectralSpace 2 (volume : Measure ℝ),
      (∀ᵐs : ℝ ∂volume,s<b → F s=0) → ∀t : ℝ,
      ‖nativeConjugatedCurve (nativeL2ParticularAngularCLM (fullBubblePhasePotential τ) F) t‖≤
        D*‖F‖*Real.exp (2*t) := by
  let P := fullBubbleHighPotential τ
  obtain ⟨D,hD,hd⟩ := exists_spectralL2Potential_far_end_decay nativeAngularRate nativeAngularRate_lower
    P.κ_nonneg P.κ_lt_one (fullBubblePhasePotential τ) P.kernel_bound
    (fullBubblePhasePotential_plus_kernel τ) (15*Real.exp (2*τ)) (by positivity)
    (fullBubblePhasePotential_left_exp_bound τ) b
  refine ⟨‖nativeHighProjection‖*D,by positivity,fun F hF t => ?_⟩
  let Z := spectralL2PotentialContinuousCLM nativeAngularRate (by norm_num : (0:ℝ)<5/2)
    nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) (fullBubblePhasePotential τ) F t
  have hz := hd F hF t
  change ‖Z‖≤D*‖F‖*Real.exp (4*t) at hz
  have hh := nativeHighProjection.le_opNorm (angularBasis.repr.symm Z)
  rw [angularBasis.repr.symm.norm_map] at hh
  change ‖Real.exp (-2*t) • nativeHighProjection (angularBasis.repr.symm Z)‖≤_
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left
    (hh.trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))) (Real.exp_pos _).le).trans_eq
  calc
    _ = (‖nativeHighProjection‖*D)*‖F‖*(Real.exp (-2*t)*Real.exp (4*t)) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring

#print axioms fullBubblePhasePotential_left_exp_bound
#print axioms exists_nativeBubbleParticular_far_end_bound
end Yamabe3.Analysis.SpherePolar
