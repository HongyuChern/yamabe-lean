import Yamabe3.Analysis.BubbleLowCauchyExplicit

/-! Newton-rate decay of the SAME chosen compensated low Cauchy field.
The explicit representation is proved by Cauchy uniqueness, then two
unit data give a constant before arbitrary entrance values. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

private theorem unit_far (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {τ : ℝ} (ht : 0 < τ) (d n : ℝ) :
    ∃M : ℝ, 0 ≤ M ∧ ∀t : ℝ, t ≤ 0 →
      ‖bubbleLowZeroCauchyLinear i hi ht (d,n) t‖ ≤ M*Real.exp (t/2) ∧
        ‖deriv (bubbleLowZeroCauchyLinear i hi ht (d,n)) t‖ ≤ M*Real.exp (t/2) := by
  let c := bubbleLowCauchyCompensation i τ d n 0
  let Hc := bubbleLowCompensatedSource i (0 : ℝ →ᵇ ℝ) c
  let P := bubbleLowPastField i hi Hc
  let a := (d+P τ)/bubbleLowJacobi i τ
  let q := bubbleLowZeroCauchyLinear i hi ht (d,n)
  have hq : q = fun t => -P t+a*bubbleLowJacobi i t :=
    bubbleLowZeroCauchyLinear_eq_explicit i hi ht d n
  have hP := (bubbleLowPastField_C2_equation i hi Hc).1
  have hd (t : ℝ) : deriv (fun s => -P s+a*bubbleLowJacobi i s) t =
      -deriv P t+a*deriv (bubbleLowJacobi i) t :=
    (((hP.differentiable (by norm_num) t).hasDerivAt.neg).add
      (((bubbleLowJacobi_smooth i).differentiable (by simp) t).hasDerivAt.const_mul a)).deriv
  let M := 4*‖Hc‖+8*|a|
  have hM : 0 ≤ M := by positivity
  refine ⟨M,hM,fun t ht0 => ?_⟩
  have he : Real.exp (2*t) ≤ Real.exp (t/2) := Real.exp_le_exp.mpr (by linarith)
  have hp := bubbleLowPastField_bounds i hi Hc t
  have hP0 : |P t| ≤ 2*‖Hc‖*Real.exp (t/2) :=
    hp.1.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hP1 : |deriv P t| ≤ 4*‖Hc‖*Real.exp (t/2) :=
    hp.2.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hJ := bubbleLowJacobi_value_far_rate i t ht0
  have hJ1 := (bubbleLowJacobi_derivatives_far_rate i hi t ht0).1
  constructor
  · change ‖q t‖ ≤ _
    rw [hq,Real.norm_eq_abs]
    have hneg : |-P t| ≤ 2*‖Hc‖*Real.exp (t/2) := by simpa only [abs_neg] using hP0
    have hprod : |a*bubbleLowJacobi i t| ≤ |a| *Real.exp (t/2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hJ (abs_nonneg a)
    have hb : |-P t+a*bubbleLowJacobi i t| ≤
        (2*‖Hc‖+|a|)*Real.exp (t/2) := by
      exact ((abs_add_le _ _).trans (add_le_add hneg hprod)).trans_eq (by ring)
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp only [M];nlinarith [norm_nonneg Hc,abs_nonneg a]) (Real.exp_pos _).le)
  · change ‖deriv q t‖ ≤ _
    rw [hq,hd,Real.norm_eq_abs]
    have hneg : |-deriv P t| ≤ 4*‖Hc‖*Real.exp (t/2) := by simpa only [abs_neg] using hP1
    have hprod : |a*deriv (bubbleLowJacobi i) t| ≤ |a| *(8*Real.exp (t/2)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hJ1 (abs_nonneg a)
    exact ((abs_add_le _ _).trans (add_le_add hneg hprod)).trans_eq (by dsimp only [M];ring)

theorem bubbleLowZeroCauchyLinear_far_rate (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {τ : ℝ} (ht : 0 < τ) :
    ∃M : ℝ, 0 ≤ M ∧ ∀d n t : ℝ, t ≤ 0 →
      ‖bubbleLowZeroCauchyLinear i hi ht (d,n) t‖ ≤ M*max ‖d‖ ‖n‖*Real.exp (t/2) ∧
        ‖deriv (bubbleLowZeroCauchyLinear i hi ht (d,n)) t‖ ≤ M*max ‖d‖ ‖n‖*Real.exp (t/2) := by
  let a := bubbleLowZeroCauchyLinear i hi ht (1,0)
  let b := bubbleLowZeroCauchyLinear i hi ht (0,1)
  have ha := (bubbleLowZeroCauchyLinear_spec i hi ht 1 0).1
  have hb := (bubbleLowZeroCauchyLinear_spec i hi ht 0 1).1
  obtain ⟨A,hA,hAb⟩ := unit_far i hi ht 1 0
  obtain ⟨B,hB,hBb⟩ := unit_far i hi ht 0 1
  refine ⟨A+B,add_nonneg hA hB,fun d n t ht0 => ?_⟩
  have he : bubbleLowZeroCauchyLinear i hi ht (d,n)=fun t => d*a t+n*b t := by
    have hv : (d,n)=d • ((1,0) : ℝ×ℝ)+n • ((0,1) : ℝ×ℝ) := by ext <;> simp
    rw [hv,map_add,map_smul,map_smul]
    rfl
  have hd : deriv (fun t => d*a t+n*b t)=fun t => d*deriv a t+n*deriv b t := by
    funext t
    exact (((ha.differentiable (by norm_num) t).hasDerivAt.const_mul d).add
      ((hb.differentiable (by norm_num) t).hasDerivAt.const_mul n)).deriv
  have hbound {x y : ℝ} (hx : ‖x‖ ≤ A*Real.exp (t/2)) (hy : ‖y‖ ≤ B*Real.exp (t/2)) :
      ‖d*x+n*y‖ ≤ (A+B)*max ‖d‖ ‖n‖*Real.exp (t/2) := by
    calc
      _ ≤ ‖d*x‖+‖n*y‖ := norm_add_le _ _
      _ ≤ max ‖d‖ ‖n‖*(A*Real.exp (t/2))+max ‖d‖ ‖n‖*(B*Real.exp (t/2)) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul (le_max_left _ _) hx (norm_nonneg _) (by positivity))
          (mul_le_mul (le_max_right _ _) hy (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [he,hd]
  exact ⟨hbound (hAb t ht0).1 (hBb t ht0).1,hbound (hAb t ht0).2 (hBb t ht0).2⟩

#print axioms bubbleLowZeroCauchyLinear_far_rate
end Yamabe3.Analysis.Delaunay
