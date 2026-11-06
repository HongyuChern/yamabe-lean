import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Finite regularity and literal third/fourth derivatives of an actual
second-order solution. No higher derivative of the solution is supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem scalar_ode_C4_on_open {O : Set ℝ} (hO : IsOpen O)
    {z q : ℝ → ℝ} (hz : ContDiffOn ℝ 2 z O) (hq : ContDiffOn ℝ 2 q O)
    (heq : ∀ t ∈ O, deriv (deriv z) t = q t * z t) :
    ContDiffOn ℝ 4 z O := by
  have hd : ContDiffOn ℝ 1 (deriv z) O := hz.deriv_of_isOpen hO (by norm_num)
  have hdd : ContDiffOn ℝ 2 (deriv (deriv z)) O :=
    (hq.mul hz).congr (fun t ht => heq t ht)
  have hd3 : ContDiffOn ℝ 3 (deriv z) O := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen hO (n := (2 : ℕ∞ω))).mpr
    exact ⟨hd.differentiableOn (by norm_num), by simp, hdd⟩
  apply (contDiffOn_succ_iff_deriv_of_isOpen hO (n := (3 : ℕ∞ω))).mpr
  exact ⟨hz.differentiableOn (by norm_num), by simp, hd3⟩

theorem scalar_ode_third_derivative {O : Set ℝ} (hO : IsOpen O)
    {z q : ℝ → ℝ} (hz : ContDiffOn ℝ 2 z O) (hq : ContDiffOn ℝ 2 q O)
    (heq : ∀ t ∈ O, deriv (deriv z) t = q t * z t) {t : ℝ} (ht : t ∈ O) :
    deriv (deriv (deriv z)) t = deriv q t * z t + q t * deriv z t := by
  have hdq := (hq.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hdz := (hz.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hlocal : deriv (deriv z) =ᶠ[𝓝 t] fun s => q s * z s :=
    (hO.eventually_mem ht).mono (fun s hs => heq s hs)
  exact hlocal.deriv_eq.trans ((hdq.hasDerivAt.mul hdz.hasDerivAt).deriv)

theorem scalar_ode_fourth_derivative {O : Set ℝ} (hO : IsOpen O)
    {z q : ℝ → ℝ} (hz : ContDiffOn ℝ 2 z O) (hq : ContDiffOn ℝ 2 q O)
    (heq : ∀ t ∈ O, deriv (deriv z) t = q t * z t) {t : ℝ} (ht : t ∈ O) :
    deriv (deriv (deriv (deriv z))) t =
      deriv (deriv q) t * z t + 2 * deriv q t * deriv z t + q t ^ 2 * z t := by
  have hz1 := (hz.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hq1 := (hq.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hzd : ContDiffOn ℝ 1 (deriv z) O := hz.deriv_of_isOpen hO (by norm_num)
  have hqd : ContDiffOn ℝ 1 (deriv q) O := hq.deriv_of_isOpen hO (by norm_num)
  have hz2 := (hzd.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hq2 := (hqd.contDiffAt (hO.mem_nhds ht)).differentiableAt (by norm_num)
  have hlocal : deriv (deriv (deriv z)) =ᶠ[𝓝 t]
      fun s => deriv q s * z s + q s * deriv z s :=
    (hO.eventually_mem ht).mono (fun s hs => scalar_ode_third_derivative hO hz hq heq hs)
  have hd : HasDerivAt (fun s => deriv q s * z s + q s * deriv z s)
      ((deriv (deriv q) t * z t + deriv q t * deriv z t) +
        (deriv q t * deriv z t + q t * deriv (deriv z) t)) t := by
    simpa only [Pi.add_apply, Pi.mul_apply] using!
      (hq2.hasDerivAt.mul hz1.hasDerivAt).add (hq1.hasDerivAt.mul hz2.hasDerivAt)
  rw [hlocal.deriv_eq, hd.deriv, heq t ht]
  ring

#print axioms scalar_ode_C4_on_open
#print axioms scalar_ode_third_derivative
#print axioms scalar_ode_fourth_derivative
end Yamabe3.Analysis.Delaunay
