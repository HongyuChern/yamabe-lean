import Yamabe3.Analysis.NativeLowL2PhysicalCollar
import Yamabe3.Analysis.NativeFiniteReverseCollarEnergy
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! The reversed actual low L2 field has genuine H2 collar estimates.
The reversal is applied to the same produced function and its source,
retaining exp(2t), the reflected potential, and the finite low spectrum. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem second_deriv_neg (q : ℝ→ℝ) (t : ℝ) :
    deriv (deriv (fun s => q (-s))) t=deriv (deriv q) (-t) := by
  rw [show deriv (fun s => q (-s))=fun s => -deriv q (-s) from funext (fun s => deriv_comp_neg q s)]
  change deriv (-(fun s => deriv q (-s))) t=_
  rw [deriv.neg,deriv_comp_neg,neg_neg]

theorem nativeLowL2_reversed_coefficient_C2 (v : ℝ→ℝ) (hv : Continuous v)
    (hb : ∀t,0≤v t ∧ v t≤1) (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2)
    (i : AngularIndex) (hi : angularEigenvalue i<6) :
    let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb)
      (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
    let q := fun t => Real.exp (2*t)*U (-t) i
    ContDiff ℝ 2 q ∧ ∀t,deriv (deriv q) t=
      (angularEigenvalue i+1/4-(15/4)*v (-t)^4)*q t+Real.exp (2*t)*F (-t) i := by
  dsimp only
  let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb)
    (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
  let q := fun t => Real.exp (-2*t)*U t i
  have h := nativeLowL2_weighted_coefficient_C2 v hv hb F hF i hi
  change ContDiff ℝ 2 q ∧ _ at h
  have he : (fun t => Real.exp (2*t)*U (-t) i)=fun t => q (-t) := by
    funext t; dsimp [q]; congr 2; ring
  change ContDiff ℝ 2 (fun t => Real.exp (2*t)*U (-t) i) ∧ _
  rw [he]
  refine ⟨h.1.comp contDiff_neg,fun t => ?_⟩
  rw [second_deriv_neg]
  have hh := h.2 (-t)
  simpa only [show (-2:ℝ)*(-t)=2*t by ring] using hh

def nativeLowReverseL2PhysicalField (v : ℝ→ℝ) (hv : Continuous v)
    (hb : ∀t,0≤v t ∧ v t≤1) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) : E→ℝ :=
  finitePhysical nativeLowIndexFinset (fun i t => Real.exp (2*t)*
    lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) F (-t) i)

theorem nativeLowReverseL2Physical_collar_energy (v : ℝ→ℝ) (hv : Continuous v)
    (hb : ∀t,0≤v t ∧ v t≤1) (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2) :
    let u := nativeLowReverseL2PhysicalField v hv hb (hF.toLp F)
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
      IntegrableOn (fun x => u x^2) O ∧
      IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫x in O,u x^2)+(∫x in O,nativeCoordinateLaplacian u x^2))≤
        (4*Real.exp 2+(17/2)^2*Real.exp 6)*‖hF.toLp F‖^2 := by
  let A := lowAngularOperatorBCF v hv hb
  let V := delaunayPhasePotentialBCF v hv hb 0
  let U := lowL2ContinuousCLM A (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
  let G := fun t => F t-V t • U t
  have hVa (t : ℝ) : V t=(15/4)*v t^4 := by simp only [V,delaunayPhasePotentialBCF_apply,add_zero]
  have hV : ‖V‖≤15/4 := delaunayPhasePotentialBCF_norm_le v hv hb 0
  obtain ⟨hU,hG₂,hu,hg₂⟩ := lowL2Continuous_square_bounds A (lowAngularOperatorBCF_norm_le v hv hb) V (hF.toLp F)
  change MemLp U 2 at hU
  have hgae : (fun t => (hF.toLp F) t-V t • U t)=ᵐ[volume] G := by
    filter_upwards [hF.coeFn_toLp] with t ht
    exact congrArg (fun x => x-V t • U t) ht
  have hG : MemLp G 2 := hG₂.ae_eq hgae
  have hg : (∫t : ℝ,‖G t‖^2)≤(17/2)^2*‖hF.toLp F‖^2 := by
    have he : (∫t : ℝ,‖G t‖^2)=(∫t : ℝ,‖(hF.toLp F) t-V t • U t‖^2) :=
      integral_congr_ae (hgae.symm.fun_comp (fun x => ‖x‖^2))
    rw [he]
    apply hg₂.trans
    gcongr
    nlinarith [norm_nonneg V]
  have hq (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :=
    nativeLowL2_reversed_coefficient_C2 v hv hb F hF i ((mem_nativeLowIndexFinset i).mp hi)
  have he := native_finite_reverse_conjugated_collar_energy nativeLowIndexFinset
    (fun i t => U t i) (fun i t => G t i)
    (fun i hi => (hq i hi).1) (fun i hi t => by
      change deriv (deriv (fun t => Real.exp (2*t)*U (-t) i)) t-
        (angularEigenvalue i+1/4)*(Real.exp (2*t)*U (-t) i)=Real.exp (2*t)*(G (-t) i)
      rw [(hq i hi).2 t]
      change (angularEigenvalue i+1/4-(15/4)*v (-t)^4)*(Real.exp (2*t)*U (-t) i)+Real.exp (2*t)*F (-t) i-
        (angularEigenvalue i+1/4)*(Real.exp (2*t)*U (-t) i)=Real.exp (2*t)*(F (-t) i-V (-t)*U (-t) i)
      rw [hVa]; ring)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hU).integrable_sq)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hG).integrable_sq)
  refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.trans ?_⟩
  have hu' := (spectralL2_finite_coordinate_integral_bound U hU nativeLowIndexFinset).trans hu
  have hg' := (spectralL2_finite_coordinate_integral_bound G hG nativeLowIndexFinset).trans hg
  exact (add_le_add (mul_le_mul_of_nonneg_left hu' (Real.exp_pos 2).le)
    (mul_le_mul_of_nonneg_left hg' (Real.exp_pos 6).le)).trans_eq (by ring)

#print axioms nativeLowL2_reversed_coefficient_C2
#print axioms nativeLowReverseL2Physical_collar_energy
end Yamabe3.Analysis.SpherePolar
