import Yamabe3.Analysis.LowL2C2Coefficients
import Yamabe3.Analysis.LowL2ResidualBounds
import Yamabe3.Analysis.NativeFiniteResidualCollar
import Yamabe3.Analysis.NativeDelaunayHalfEndPotential
import Yamabe3.Analysis.SpectralL2EntranceRegularity

/-! Genuine physical value and Laplacian collar estimates for the low
L2 inverse, first on the dense continuous-source domain. The finite low
modes retain their true spherical eigenvalues and the source is unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeLowL2PhysicalField (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : E → ℝ :=
  finitePhysical nativeLowIndexFinset (fun i t => Real.exp (-2*t)*
    lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F t i)

theorem nativeLowL2Physical_collar_energy (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2) :
    let u := nativeLowL2PhysicalField v hv hb (hF.toLp F)
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
      IntegrableOn (fun x => u x^2) O ∧
      IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        (4*Real.exp 6+(17/2)^2*Real.exp 2)*‖hF.toLp F‖^2 := by
  let A := lowAngularOperatorBCF v hv hb
  let V := delaunayPhasePotentialBCF v hv hb 0
  let U := lowL2ContinuousCLM A (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
  let G := fun t => F t-V t • U t
  have hVa (t : ℝ) : V t=(15/4)*v t^4 := by simp only [V,delaunayPhasePotentialBCF_apply,add_zero]
  have hV : ‖V‖ ≤ 15/4 := delaunayPhasePotentialBCF_norm_le v hv hb 0
  obtain ⟨hU,hG₂,hu,hg₂⟩ := lowL2Continuous_square_bounds A (lowAngularOperatorBCF_norm_le v hv hb) V (hF.toLp F)
  change MemLp U 2 at hU
  have hgae : (fun t => (hF.toLp F) t-V t • U t)=ᵐ[volume]G := by
    filter_upwards [hF.coeFn_toLp] with t ht
    exact congrArg (fun x => x-V t • U t) ht
  have hG : MemLp G 2 := hG₂.ae_eq hgae
  have hg : (∫ t : ℝ,‖G t‖^2) ≤ (17/2)^2*‖hF.toLp F‖^2 := by
    have he : (∫ t : ℝ,‖G t‖^2)=(∫ t : ℝ,‖(hF.toLp F) t-V t • U t‖^2) :=
      integral_congr_ae (hgae.symm.mono (fun t ht => congrArg (fun x => ‖x‖^2) ht))
    rw [he]
    apply hg₂.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hq (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :=
    nativeLowL2_weighted_coefficient_C2 v hv hb F hF i ((mem_nativeLowIndexFinset i).mp hi)
  have he := native_finite_conjugated_collar_energy nativeLowIndexFinset (fun i t => U t i) (fun i t => G t i)
    (fun i hi => (hq i hi).1) (fun i hi t => by
      change deriv (deriv (fun t => Real.exp (-2*t)*U t i)) t-
        (angularEigenvalue i+1/4)*(Real.exp (-2*t)*U t i)=Real.exp (-2*t)*(G t i)
      rw [(hq i hi).2 t]
      change (angularEigenvalue i+1/4-(15/4)*v t^4)*(Real.exp (-2*t)*U t i)+Real.exp (-2*t)*F t i-
        (angularEigenvalue i+1/4)*(Real.exp (-2*t)*U t i)=Real.exp (-2*t)*(F t i-V t*U t i)
      rw [hVa]
      ring)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hU).integrable_sq)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hG).integrable_sq)
  refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.trans ?_⟩
  have hu' := (spectralL2_finite_coordinate_integral_bound U hU nativeLowIndexFinset).trans hu
  have hg' := (spectralL2_finite_coordinate_integral_bound G hG nativeLowIndexFinset).trans hg
  exact (add_le_add (mul_le_mul_of_nonneg_left hu' (Real.exp_pos 6).le)
    (mul_le_mul_of_nonneg_left hg' (Real.exp_pos 2).le)).trans_eq (by ring)

#print axioms nativeLowL2Physical_collar_energy
end Yamabe3.Analysis.SpherePolar
