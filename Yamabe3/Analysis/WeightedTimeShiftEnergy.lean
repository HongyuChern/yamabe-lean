import Yamabe3.Analysis.NativePoissonReflectedEnergy
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Exact derivative and whole-line square-integral identities for the
physical weighted time shift. These identities are later applied to the
same entrance extension, without selecting a new half-end solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

def weightedTimeShift (s : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (2*s)*f (t+s)

theorem weightedTimeShift_C2 (s : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (weightedTimeShift s f) := by
  unfold weightedTimeShift
  exact contDiff_const.mul (hf.comp (contDiff_id.add contDiff_const))

theorem weightedTimeShift_deriv (s : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (weightedTimeShift s f)=weightedTimeShift s (deriv f) := by
  funext t
  exact ((((hf (t+s)).hasDerivAt).comp t ((hasDerivAt_id t).add_const s)).const_mul
    (Real.exp (2*s))).deriv.trans (by simp [weightedTimeShift])

theorem weightedTimeShift_second (s : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    deriv (deriv (weightedTimeShift s f))=weightedTimeShift s (deriv (deriv f)) := by
  rw [weightedTimeShift_deriv s (hf.differentiable (by norm_num))]
  have hf1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  exact weightedTimeShift_deriv s (hf1.differentiable (by norm_num))

theorem weightedTimeShift_square_integrable (s : ℝ) {f : ℝ → ℝ}
    (hf : Integrable (fun t => f t^2) (volume : Measure ℝ)) :
    Integrable (fun t => weightedTimeShift s f t^2) (volume : Measure ℝ) := by
  have h := ((measurePreserving_add_right volume s).integrable_comp_of_integrable hf).const_mul
    (Real.exp (2*s)^2)
  simpa only [weightedTimeShift,mul_pow,Function.comp_def] using h

theorem weightedTimeShift_square_integral (s : ℝ) (f : ℝ → ℝ) :
    (∫ t : ℝ,weightedTimeShift s f t^2)=Real.exp (4*s)*(∫ t : ℝ,f t^2) := by
  simp only [weightedTimeShift,mul_pow]
  rw [integral_const_mul,integral_add_right_eq_self (μ := volume) (fun t => f t^2) s,←Real.exp_nat_mul]
  congr 2
  ring

#print axioms weightedTimeShift_C2
#print axioms weightedTimeShift_deriv
#print axioms weightedTimeShift_second
#print axioms weightedTimeShift_square_integrable
#print axioms weightedTimeShift_square_integral
end Yamabe3.Analysis.Delaunay
