import Yamabe3.Analysis.DelaunayPhaseData
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Actual phase-uniform time jets of the original Delaunay potential.
The derivative constants are consequences of the same bounded ODE orbit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay
variable {κ : ℝ}

theorem DelaunayPhaseData.potential_deriv (p : DelaunayPhaseData κ) (t : ℝ) :
    deriv (fun s => p.potential s) t = 15 * p.orbit (t+p.phase)^3 * deriv p.orbit (t+p.phase) := by
  have h := ((((p.smooth.differentiable (by simp) (t+p.phase)).hasDerivAt).comp t
    ((hasDerivAt_id t).add_const p.phase)).pow 4).const_mul (15/4:ℝ)
  have hd : HasDerivAt (fun s => p.potential s)
      (15 * p.orbit (t+p.phase)^3 * deriv p.orbit (t+p.phase)) t := by
    apply h.congr_deriv
    simp only [Function.comp_def, id_eq, Pi.pow_apply, mul_one]
    ring
  exact hd.deriv

theorem DelaunayPhaseData.potential_second_deriv (p : DelaunayPhaseData κ) (t : ℝ) :
    deriv (deriv (fun s => p.potential s)) t =
      45 * p.orbit (t+p.phase)^2 * (deriv p.orbit (t+p.phase))^2 +
        15 * p.orbit (t+p.phase)^3 * radialForce (p.orbit (t+p.phase)) := by
  have hv := (p.smooth.differentiable (by simp) (t+p.phase)).hasDerivAt.comp t
    ((hasDerivAt_id t).add_const p.phase)
  have hvd := ((p.smooth.deriv' (n := ∞)).differentiable (by simp) (t+p.phase)).hasDerivAt.comp t
    ((hasDerivAt_id t).add_const p.phase)
  have hfun : deriv (fun s => p.potential s) =
      fun s => 15 * p.orbit (s+p.phase)^3 * deriv p.orbit (s+p.phase) :=
    funext p.potential_deriv
  rw [hfun]
  have hd := ((hv.pow 3).const_mul 15).mul hvd
  have hd' : HasDerivAt
      (fun s => 15 * p.orbit (s+p.phase)^3 * deriv p.orbit (s+p.phase))
      (45 * p.orbit (t+p.phase)^2 * (deriv p.orbit (t+p.phase))^2 +
        15 * p.orbit (t+p.phase)^3 * radialForce (p.orbit (t+p.phase))) t := by
    apply hd.congr_deriv
    simp only [Function.comp_def, id_eq, Pi.pow_apply, mul_one, p.ode]
    ring
  exact hd'.deriv

theorem DelaunayPhaseData.potential_time_jets_bound (p : DelaunayPhaseData κ) (t : ℝ) :
    |deriv (fun s => p.potential s) t| ≤ 15/2 ∧
      |deriv (deriv (fun s => p.potential s)) t| ≤ 105/4 := by
  let x := p.orbit (t+p.phase)
  let y := deriv p.orbit (t+p.phase)
  have hx := p.bounded (t+p.phase)
  have hy := p.derivative_bound (t+p.phase)
  change 0 ≤ x ∧ x ≤ 1 at hx
  change |y| ≤ 1/2 at hy
  have hx2 : x^2 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hx3 : x^3 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hx5 : x^5 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hf : |radialForce x| ≤ 1 := by
    rw [radialForce]
    apply (abs_sub _ _).trans
    rw [abs_div, abs_div, abs_mul, abs_of_nonneg hx.1, abs_of_nonneg (pow_nonneg hx.1 5)]
    norm_num
    linarith only [hx.2, hx5]
  have hy2 : y^2 ≤ 1/4 := by
    have h := sq_le_sq₀ (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1/2)
    have hh := h.mpr hy
    norm_num only [sq_abs] at hh
    nlinarith only [hh]
  constructor
  · rw [p.potential_deriv]
    change |15*x^3*y| ≤ 15/2
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx.1 3)]
    norm_num
    have h := mul_le_mul hx3 hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [h]
  · rw [p.potential_second_deriv]
    change |45*x^2*y^2+15*x^3*radialForce x| ≤ 105/4
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (by positivity : 0 ≤ 45*x^2*y^2), abs_mul,
      abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 15) (pow_nonneg hx.1 3))]
    have h1 := mul_le_mul hx2 hy2 (sq_nonneg y) (by norm_num : (0:ℝ) ≤ 1)
    have h2 := mul_le_mul hx3 hf (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [h1, h2]

#print axioms DelaunayPhaseData.potential_deriv
#print axioms DelaunayPhaseData.potential_second_deriv
#print axioms DelaunayPhaseData.potential_time_jets_bound
end Yamabe3.Analysis.Delaunay
