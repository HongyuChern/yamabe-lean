import Yamabe3.Analysis.NativeBubbleHighPotential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! The actual full-bubble potential has uniform time jets, before its
phase is chosen. Rational exponential identities retain the same density. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

def fullBubbleSlope (t : ℝ) : ℝ := (1-Real.exp (2*t))/(1+Real.exp (2*t))

theorem fullBubbleSlope_bound (t : ℝ) : |fullBubbleSlope t| ≤ 1 := by
  unfold fullBubbleSlope
  rw [abs_div, abs_of_pos (by positivity : 0 < 1+Real.exp (2*t))]
  apply (div_le_iff₀ (by positivity : 0 < 1+Real.exp (2*t))).mpr
  rw [one_mul, abs_le]
  have he := Real.exp_pos (2*t)
  constructor <;> linarith

theorem fullBubbleSlope_hasDeriv (t : ℝ) :
    HasDerivAt fullBubbleSlope (-fullBubbleDensity t) t := by
  have he := ((hasDerivAt_id t).const_mul 2).exp
  have h := ((hasDerivAt_const t (1:ℝ)).sub he).div
    ((hasDerivAt_const t (1:ℝ)).add he) (ne_of_gt (by positivity : 0 < 1+Real.exp (2*t)))
  apply h.congr_deriv
  dsimp only [fullBubbleDensity, id_eq, Pi.add_apply, Pi.sub_apply]
  field_simp
  <;> ring

theorem fullBubbleDensity_hasDeriv (t : ℝ) :
    HasDerivAt fullBubbleDensity (2*fullBubbleDensity t*fullBubbleSlope t) t := by
  have he := ((hasDerivAt_id t).const_mul 2).exp
  have h := (he.const_mul 4).div (((hasDerivAt_const t (1:ℝ)).add he).pow 2)
    (pow_ne_zero 2 (ne_of_gt (by positivity : 0 < 1+Real.exp (2*t))))
  apply h.congr_deriv
  dsimp only [fullBubbleDensity, fullBubbleSlope, id_eq, Pi.add_apply, Pi.pow_apply]
  field_simp
  <;> ring

theorem fullBubbleDensity_second_deriv (t : ℝ) :
    deriv (deriv fullBubbleDensity) t =
      4*fullBubbleDensity t*(fullBubbleSlope t)^2-2*(fullBubbleDensity t)^2 := by
  have heq : deriv fullBubbleDensity = fun s => 2*fullBubbleDensity s*fullBubbleSlope s :=
    funext (fun s => (fullBubbleDensity_hasDeriv s).deriv)
  rw [heq]
  have h := ((fullBubbleDensity_hasDeriv t).const_mul 2).mul (fullBubbleSlope_hasDeriv t)
  exact h.deriv.trans (by ring)

theorem fullBubbleDensity_smooth : ContDiff ℝ ∞ fullBubbleDensity := by
  unfold fullBubbleDensity
  apply ContDiff.div (by fun_prop) (by fun_prop)
  intro t
  exact pow_ne_zero 2 (ne_of_gt (by positivity : 0 < 1+Real.exp (2*t)))

theorem fullBubbleDensity_time_jets_bound (t : ℝ) :
    |deriv fullBubbleDensity t| ≤ 2 ∧ |deriv (deriv fullBubbleDensity) t| ≤ 6 := by
  have hd := fullBubbleDensity_bounds t
  have hs := fullBubbleSlope_bound t
  have hd2 := pow_le_one₀ hd.1 hd.2 (n:=2)
  have hs2 : fullBubbleSlope t^2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (fullBubbleSlope t)) (by norm_num : (0:ℝ) ≤ 1)).mpr hs
    simpa only [sq_abs, one_pow] using h
  constructor
  · rw [(fullBubbleDensity_hasDeriv t).deriv, abs_mul,
      abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd.1)]
    have h := mul_le_mul hd.2 hs (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [h]
  · rw [fullBubbleDensity_second_deriv]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hd.1)
      (sq_nonneg _)), abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg _))]
    have h := mul_le_mul hd.2 hs2 (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [h, hd2]

theorem fullBubbleHighPotential_time_jets (τ : ℝ) :
    ContDiff ℝ ∞ (fun t => (fullBubbleHighPotential τ).potential t) ∧
      ∀ t : ℝ, |deriv (fun s => (fullBubbleHighPotential τ).potential s) t| ≤ 15/2 ∧
        |deriv (deriv (fun s => (fullBubbleHighPotential τ).potential s)) t| ≤ 45/2 := by
  have hfun : (fun t => (fullBubbleHighPotential τ).potential t) =
      fun t => (15/4:ℝ)*fullBubbleDensity (t+τ) := rfl
  rw [hfun]
  refine ⟨contDiff_const.mul (fullBubbleDensity_smooth.comp (contDiff_id.add contDiff_const)), ?_⟩
  intro t
  have hd : deriv (fun s => (15/4:ℝ)*fullBubbleDensity (s+τ)) =
      fun s => (15/4:ℝ)*deriv fullBubbleDensity (s+τ) := by
    funext s
    simpa only [Function.comp_def, id_eq, mul_one] using
      (((fullBubbleDensity_smooth.differentiable (by simp) (s+τ)).hasDerivAt.comp s
        ((hasDerivAt_id s).add_const τ)).const_mul (15/4:ℝ)).deriv
  have hdd : deriv (fun s => (15/4:ℝ)*deriv fullBubbleDensity (s+τ)) t =
      (15/4:ℝ)*deriv (deriv fullBubbleDensity) (t+τ) := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      ((((fullBubbleDensity_smooth.deriv' (n:=∞)).differentiable (by simp) (t+τ)).hasDerivAt.comp t
        ((hasDerivAt_id t).add_const τ)).const_mul (15/4:ℝ)).deriv
  rw [hd, hdd]
  have h := fullBubbleDensity_time_jets_bound (t+τ)
  simp only [abs_mul]
  norm_num only [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 15), abs_of_pos (by norm_num : (0:ℝ) < 4)]
  constructor <;> linarith only [h.1,h.2]

#print axioms fullBubbleSlope_hasDeriv
#print axioms fullBubbleDensity_hasDeriv
#print axioms fullBubbleDensity_second_deriv
#print axioms fullBubbleHighPotential_time_jets
end Yamabe3.Analysis.Delaunay
