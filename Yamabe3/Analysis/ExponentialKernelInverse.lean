import Yamabe3.Analysis.ExponentialTailIntegrals
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The genuine constant-mass inverse on the line

The inverse of d²/dt²-k² is defined by actual exponentially weighted
half-line integrals. For k>0 it takes bounded continuous sources to twice
differentiable functions, satisfies the real differential equation and has
operator bound k⁻². This is the analytic kernel used in the high-mode
contraction, rather than an assumed right inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def massInverse (k : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.exp (-k * t) * leftTail (fun s => Real.exp (k * s) * F s) t +
    Real.exp (k * t) * rightTail (fun s => Real.exp (-k * s) * F s) t) / (-2 * k)

theorem exp_source_integrable {k : ℝ} (hk : 0 < k) {F : ℝ → ℝ}
    (hF : Continuous F) {A : ℝ} (hbound : ∀ t, |F t| ≤ A) (t : ℝ) :
    IntegrableOn (fun s => Real.exp (k * s) * F s) (Iic t) ∧
      IntegrableOn (fun s => Real.exp (-k * s) * F s) (Ioi t) := by
  have hb (a s : ℝ) : ‖Real.exp (a * s) * F s‖ ≤ A * Real.exp (a * s) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    simpa only [mul_comm A] using mul_le_mul_of_nonneg_left (hbound s) (Real.exp_pos _).le
  constructor
  · apply ((integrableOn_exp_mul_Iic hk t).const_mul A).mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF).aestronglyMeasurable.restrict
    exact Eventually.of_forall (hb k)
  · apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) t).const_mul A).mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF).aestronglyMeasurable.restrict
    exact Eventually.of_forall (hb (-k))

theorem exp_tail_bounds {k : ℝ} (hk : 0 < k) {F : ℝ → ℝ}
    {A : ℝ} (hbound : ∀ t, |F t| ≤ A) (t : ℝ) :
    |leftTail (fun s => Real.exp (k * s) * F s) t| ≤ A * Real.exp (k * t) / k ∧
      |rightTail (fun s => Real.exp (-k * s) * F s) t| ≤ A * Real.exp (-k * t) / k := by
  have hb (a s : ℝ) : ‖Real.exp (a * s) * F s‖ ≤ A * Real.exp (a * s) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    simpa only [mul_comm A] using mul_le_mul_of_nonneg_left (hbound s) (Real.exp_pos _).le
  constructor
  · have h := norm_integral_le_of_norm_le (f := fun s => Real.exp (k * s) * F s)
      ((integrableOn_exp_mul_Iic hk t).const_mul A) (Eventually.of_forall (hb k))
    simpa only [leftTail, Real.norm_eq_abs, integral_const_mul, integral_exp_mul_Iic hk,
      mul_div_assoc] using h
  · have h := norm_integral_le_of_norm_le (f := fun s => Real.exp (-k * s) * F s)
      ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) t).const_mul A)
      (Eventually.of_forall (hb (-k)))
    simpa only [rightTail, Real.norm_eq_abs, integral_const_mul,
      integral_exp_mul_Ioi (neg_neg_of_pos hk), neg_div_neg_eq, mul_div_assoc] using h

theorem massInverse_bound {k : ℝ} (hk : 0 < k) {F : ℝ → ℝ}
    {A : ℝ} (hbound : ∀ t, |F t| ≤ A) (t : ℝ) :
    |massInverse k F t| ≤ A / k ^ 2 := by
  obtain ⟨hL, hR⟩ := exp_tail_bounds hk hbound t
  have he : Real.exp (-k * t) * Real.exp (k * t) = 1 := by
    rw [← Real.exp_add, show -k * t + k * t = 0 by ring, Real.exp_zero]
  have htermL : |Real.exp (-k * t) * leftTail (fun s => Real.exp (k * s) * F s) t| ≤ A / k := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-k * t) * (A * Real.exp (k * t) / k) :=
        mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
      _ = A / k * (Real.exp (-k * t) * Real.exp (k * t)) := by ring
      _ = _ := by rw [he, mul_one]
  have htermR : |Real.exp (k * t) * rightTail (fun s => Real.exp (-k * s) * F s) t| ≤ A / k := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (k * t) * (A * Real.exp (-k * t) / k) :=
        mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
      _ = A / k * (Real.exp (-k * t) * Real.exp (k * t)) := by ring
      _ = _ := by rw [he, mul_one]
  have hn := (abs_add_le
    (Real.exp (-k * t) * leftTail (fun s => Real.exp (k * s) * F s) t)
    (Real.exp (k * t) * rightTail (fun s => Real.exp (-k * s) * F s) t)).trans
    (add_le_add htermL htermR)
  unfold massInverse
  rw [abs_div, abs_of_neg (by linarith : -2 * k < 0)]
  calc
    _ ≤ (A / k + A / k) / -(-2 * k) := div_le_div_of_nonneg_right hn (by linarith)
    _ = _ := by field_simp; ring

private theorem exp_mul_derivative (k t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (k * s)) (k * Real.exp (k * t)) t := by
  apply (((hasDerivAt_id t).const_mul k).exp).congr_deriv
  simp only [id_eq]
  ring

/-- Both differentiations of the actual integral are proved for continuous
bounded sources; no differentiability of the source is needed. -/
theorem massInverse_differentiable_equation {k : ℝ} (hk : 0 < k) {F : ℝ → ℝ}
    (hF : Continuous F) {A : ℝ} (hbound : ∀ t, |F t| ≤ A) :
    Differentiable ℝ (massInverse k F) ∧
      Differentiable ℝ (deriv (massInverse k F)) ∧
      ∀ t, deriv (deriv (massInverse k F)) t = k ^ 2 * massInverse k F t + F t := by
  let L := leftTail (fun s => Real.exp (k * s) * F s)
  let R := rightTail (fun s => Real.exp (-k * s) * F s)
  have hLi : ∀ t, IntegrableOn (fun s => Real.exp (k * s) * F s) (Iic t) :=
    fun t => (exp_source_integrable hk hF hbound t).1
  have hRi : ∀ t, IntegrableOn (fun s => Real.exp (-k * s) * F s) (Ioi t) :=
    fun t => (exp_source_integrable hk hF hbound t).2
  have hLd (t : ℝ) : HasDerivAt L (Real.exp (k * t) * F t) t :=
    leftTail_hasDerivAt
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF) hLi t
  have hRd (t : ℝ) : HasDerivAt R (-(Real.exp (-k * t) * F t)) t :=
    rightTail_hasDerivAt
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF) hRi t
  let J : ℝ → ℝ := fun t => (Real.exp (-k * t) * L t - Real.exp (k * t) * R t) / 2
  have hd (t : ℝ) : HasDerivAt (massInverse k F) (J t) t := by
    apply ((((exp_mul_derivative (-k) t).mul (hLd t)).add
      ((exp_mul_derivative k t).mul (hRd t))).div_const (-2 * k)).congr_deriv
    dsimp [J]
    field_simp
    ring
  have hid : deriv (massInverse k F) = J := funext fun t => (hd t).deriv
  have hJd (t : ℝ) : HasDerivAt J (k ^ 2 * massInverse k F t + F t) t := by
    apply ((((exp_mul_derivative (-k) t).mul (hLd t)).sub
      ((exp_mul_derivative k t).mul (hRd t))).div_const 2).congr_deriv
    have he : Real.exp (-k * t) * Real.exp (k * t) = 1 := by
      rw [← Real.exp_add, show -k * t + k * t = 0 by ring, Real.exp_zero]
    change _ = k ^ 2 * ((Real.exp (-k * t) * L t + Real.exp (k * t) * R t) / (-2 * k)) + F t
    field_simp
    simp only [neg_mul] at he
    nlinarith [congrArg (fun z : ℝ => z * F t) he]
  refine ⟨fun t => (hd t).differentiableAt, ?_, ?_⟩
  · rw [hid]
    exact fun t => (hJd t).differentiableAt
  · intro t
    rw [hid, (hJd t).deriv]

theorem massInverse_sub {k : ℝ} (hk : 0 < k) {F H : ℝ → ℝ}
    (hF : Continuous F) (hH : Continuous H) {A B : ℝ}
    (hFb : ∀ t, |F t| ≤ A) (hHb : ∀ t, |H t| ≤ B) :
    massInverse k (fun t => F t - H t) = fun t => massInverse k F t - massInverse k H t := by
  funext t
  obtain ⟨hFL, hFR⟩ := exp_source_integrable hk hF hFb t
  obtain ⟨hHL, hHR⟩ := exp_source_integrable hk hH hHb t
  unfold massInverse leftTail rightTail
  simp_rw [mul_sub]
  rw [integral_sub hFL hHL, integral_sub hFR hHR]
  ring

/-- The actual integral, bundled in the complete space of bounded continuous
functions for the contraction argument. -/
def massResolvent (k : ℝ) (hk : 0 < k) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (massInverse k F)
    (massInverse_differentiable_equation hk F.continuous
      (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t)).1.continuous
    (‖F‖ / k ^ 2)
    (fun t => by simpa only [Real.norm_eq_abs] using
      massInverse_bound hk (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t) t)

theorem massResolvent_norm_le {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ ℝ) :
    ‖massResolvent k hk F‖ ≤ ‖F‖ / k ^ 2 := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖massInverse k F t‖ ≤ ‖F‖ / k ^ 2
  simpa only [Real.norm_eq_abs] using
    massInverse_bound hk (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t) t

theorem massResolvent_sub {k : ℝ} (hk : 0 < k) (F H : ℝ →ᵇ ℝ) :
    massResolvent k hk (F - H) = massResolvent k hk F - massResolvent k hk H := by
  apply BoundedContinuousFunction.ext
  intro t
  exact congrFun (massInverse_sub hk F.continuous H.continuous
    (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t)
    (fun t => by simpa only [Real.norm_eq_abs] using H.norm_coe_le_norm t)) t

theorem massResolvent_dist_le {k : ℝ} (hk : 0 < k) (F H : ℝ →ᵇ ℝ) :
    dist (massResolvent k hk F) (massResolvent k hk H) ≤ dist F H / k ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm, ← massResolvent_sub hk]
  exact massResolvent_norm_le hk (F - H)

#print axioms massInverse_differentiable_equation
#print axioms massResolvent_dist_le

end Yamabe3.Analysis.Delaunay
