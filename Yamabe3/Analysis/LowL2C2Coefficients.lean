import Yamabe3.Analysis.LowL2BCFIdentification
import Yamabe3.Analysis.NativeLowC2Coefficients

/-! C2 physical low coefficients on the dense continuous L2 source domain.
The solution is still the single canonical L2 inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem lowL2Continuous_BCF_observable_C2
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) (L : H →L[ℝ] ℝ) :
    let U := lowL2ContinuousCLM A hA (hF.toLp F)
    ContDiff ℝ 2 (fun t => L (U t)) ∧
      ∀ t,deriv (deriv (fun s => L (U s))) t=
        4*deriv (fun s => L (U s)) t-4*L (U t)+L (F t)+L (A t (U t)) := by
  let U := lowL2ContinuousCLM A hA (hF.toLp F)
  have h := lowL2Continuous_BCF_equation A hA F hF
  dsimp only at h
  have hd (t : ℝ) : HasDerivAt (fun s => L (U s)) (L (deriv (fun s => U s) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (h.1 t).hasDerivAt
  have he : deriv (fun s => L (U s))=(fun t => L (deriv (fun s => U s) t)) :=
    funext fun t => (hd t).deriv
  have hd2 (t : ℝ) : HasDerivAt (fun s => L (deriv (fun t => U t) s))
      (L (deriv (deriv (fun t => U t)) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (h.2.1 t).hasDerivAt
  have hy : Differentiable ℝ (fun t => L (U t)) := fun t => (hd t).differentiableAt
  have hdy : Differentiable ℝ (deriv (fun t => L (U t))) := by
    rw [he]
    exact fun t => (hd2 t).differentiableAt
  have hode (t : ℝ) : deriv (deriv (fun s => L (U s))) t=
      4*deriv (fun s => L (U s)) t-4*L (U t)+L (F t)+L (A t (U t)) := by
    rw [he,(hd2 t).deriv,h.2.2 t]
    simp only [map_add,map_sub,map_smul,smul_eq_mul]
    rfl
  have hc : Continuous (deriv (deriv (fun t => L (U t)))) := by
    rw [funext hode]
    exact (((continuous_const.mul hdy.continuous).sub (continuous_const.mul hy.continuous)).add
      (L.continuous.comp F.continuous)).add (L.continuous.comp (A.continuous.clm_apply U.continuous))
  exact ⟨contDiff_two_of_continuous_second_deriv hy hdy hc,hode⟩

theorem nativeLowL2_weighted_coefficient_C2 (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1) (F : ℝ →ᵇ AngularSpectralSpace) (hF : MemLp F 2)
    (i : AngularIndex) (hi : angularEigenvalue i < 6) :
    let U := lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb) (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
    let q := fun t => Real.exp (-2*t)*U t i
    ContDiff ℝ 2 q ∧ ∀ t,deriv (deriv q) t=
      (angularEigenvalue i+1/4-(15/4)*v t^4)*q t+Real.exp (-2*t)*F t i := by
  let A := lowAngularOperatorBCF v hv hb
  let U := lowL2ContinuousCLM A (lowAngularOperatorBCF_norm_le v hv hb) (hF.toLp F)
  have h := lowL2Continuous_BCF_observable_C2 A (lowAngularOperatorBCF_norm_le v hv hb) F hF
    (lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i)
  change ContDiff ℝ 2 (fun t => U t i) ∧
    (∀ t,deriv (deriv (fun s => U s i)) t=4*deriv (fun s => U s i) t-4*U t i+F t i+(A t (U t)) i) at h
  have hy : Differentiable ℝ (fun t => U t i) := h.1.differentiable (by norm_num)
  have hdy : Differentiable ℝ (deriv (fun t => U t i)) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp h.1).2.2.differentiable (by norm_num)
  refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul h.1,?_⟩
  intro t
  change deriv (deriv (fun s => Real.exp (-2*s)*U s i)) t=_
  rw [exponential_conjugate_second_deriv_C2 hy hdy,h.2 t]
  have ha : (A t (U t)) i=(1/4+angularEigenvalue i-(15/4)*v t^4)*U t i := by
    change lowAngularCoefficient v t i*U t i=_
    rw [lowAngularCoefficient,if_pos hi]
  rw [ha]
  dsimp only
  ring

#print axioms lowL2Continuous_BCF_observable_C2
#print axioms nativeLowL2_weighted_coefficient_C2
end Yamabe3.Analysis.Delaunay
