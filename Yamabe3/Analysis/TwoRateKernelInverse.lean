import Yamabe3.Analysis.ExponentialKernelInverse

/-!
# Exponential inverse with two rates

This actual integral inverts d²/dt²+(r-s)d/dt-rs for positive r,s.
Its norm 1/(rs) is the precise bound needed after exponential conjugation,
so weighted high-mode estimates follow from a genuine drifted inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def twoRateInverse (r s : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.exp (-r * t) * leftTail (fun y => Real.exp (r * y) * F y) t +
    Real.exp (s * t) * rightTail (fun y => Real.exp (-s * y) * F y) t) / (-(r + s))

theorem twoRateInverse_bound {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {F : ℝ → ℝ} {A : ℝ} (hbound : ∀ t, |F t| ≤ A) (t : ℝ) :
    |twoRateInverse r s F t| ≤ A / (r * s) := by
  have hL := (exp_tail_bounds hr hbound t).1
  have hR := (exp_tail_bounds hs hbound t).2
  have htermL : |Real.exp (-r * t) * leftTail (fun y => Real.exp (r * y) * F y) t| ≤ A / r := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-r * t) * (A * Real.exp (r * t) / r) :=
        mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
      _ = A / r * Real.exp (-r * t + r * t) := by rw [Real.exp_add]; ring
      _ = _ := by rw [show -r * t + r * t = 0 by ring, Real.exp_zero, mul_one]
  have htermR : |Real.exp (s * t) * rightTail (fun y => Real.exp (-s * y) * F y) t| ≤ A / s := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (s * t) * (A * Real.exp (-s * t) / s) :=
        mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
      _ = A / s * Real.exp (s * t + -s * t) := by rw [Real.exp_add]; ring
      _ = _ := by rw [show s * t + -s * t = 0 by ring, Real.exp_zero, mul_one]
  have hn := (abs_add_le
    (Real.exp (-r * t) * leftTail (fun y => Real.exp (r * y) * F y) t)
    (Real.exp (s * t) * rightTail (fun y => Real.exp (-s * y) * F y) t)).trans
      (add_le_add htermL htermR)
  unfold twoRateInverse
  rw [abs_div, abs_neg, abs_of_pos (add_pos hr hs)]
  calc
    _ ≤ (A / r + A / s) / (r + s) :=
      div_le_div_of_nonneg_right hn (add_pos hr hs).le
    _ = _ := by field_simp; ring

private theorem exponential_derivative (a t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (a * y)) (a * Real.exp (a * t)) t := by
  apply (((hasDerivAt_id t).const_mul a).exp).congr_deriv
  simp only [id_eq]
  ring

theorem twoRateInverse_differentiable_equation {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {F : ℝ → ℝ} (hF : Continuous F) {A : ℝ} (hbound : ∀ t, |F t| ≤ A) :
    Differentiable ℝ (twoRateInverse r s F) ∧
      Differentiable ℝ (deriv (twoRateInverse r s F)) ∧
      ∀ t, deriv (deriv (twoRateInverse r s F)) t =
        (s - r) * deriv (twoRateInverse r s F) t + (r * s) * twoRateInverse r s F t + F t := by
  let L := leftTail (fun y => Real.exp (r * y) * F y)
  let R := rightTail (fun y => Real.exp (-s * y) * F y)
  have hsum : r + s ≠ 0 := (add_pos hr hs).ne'
  have hLd (t : ℝ) : HasDerivAt L (Real.exp (r * t) * F t) t :=
    leftTail_hasDerivAt
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF)
      (fun y => (exp_source_integrable hr hF hbound y).1) t
  have hRd (t : ℝ) : HasDerivAt R (-(Real.exp (-s * t) * F t)) t :=
    rightTail_hasDerivAt
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF)
      (fun y => (exp_source_integrable hs hF hbound y).2) t
  let J : ℝ → ℝ := fun t =>
    (-r * Real.exp (-r * t) * L t + s * Real.exp (s * t) * R t) / (-(r + s))
  have heL (t : ℝ) : Real.exp (-r * t) * Real.exp (r * t) = 1 := by
    rw [← Real.exp_add, show -r * t + r * t = 0 by ring, Real.exp_zero]
  have heR (t : ℝ) : Real.exp (s * t) * Real.exp (-s * t) = 1 := by
    rw [← Real.exp_add, show s * t + -s * t = 0 by ring, Real.exp_zero]
  have hd (t : ℝ) : HasDerivAt (twoRateInverse r s F) (J t) t := by
    apply ((((exponential_derivative (-r) t).mul (hLd t)).add
      ((exponential_derivative s t).mul (hRd t))).div_const (-(r + s))).congr_deriv
    dsimp [J]
    have hL := heL t
    have hR := heR t
    field_simp
    simp only [neg_mul] at hL hR
    rw [mul_comm s t] at hR
    nlinarith [congrArg (fun z : ℝ => z * F t) hL,
      congrArg (fun z : ℝ => z * F t) hR]
  have hid : deriv (twoRateInverse r s F) = J := funext fun t => (hd t).deriv
  have hJd (t : ℝ) : HasDerivAt J
      ((s - r) * J t + (r * s) * twoRateInverse r s F t + F t) t := by
    apply (((((exponential_derivative (-r) t).const_mul (-r)).mul (hLd t)).add
      (((exponential_derivative s t).const_mul s).mul (hRd t))).div_const (-(r + s))).congr_deriv
    have hL := heL t
    have hR := heR t
    change _ = (s - r) * ((-r * Real.exp (-r * t) * L t + s * Real.exp (s * t) * R t) / (-(r + s))) +
      (r * s) * ((Real.exp (-r * t) * L t + Real.exp (s * t) * R t) / (-(r + s))) + F t
    field_simp
    simp only [neg_mul] at hL hR
    rw [mul_comm s t] at hR
    nlinarith [congrArg (fun z : ℝ => z * (r * F t)) hL,
      congrArg (fun z : ℝ => z * (s * F t)) hR]
  refine ⟨fun t => (hd t).differentiableAt, ?_, ?_⟩
  · rw [hid]
    exact fun t => (hJd t).differentiableAt
  · intro t
    rw [hid, (hJd t).deriv]

theorem twoRateInverse_sub {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {F H : ℝ → ℝ} (hF : Continuous F) (hH : Continuous H) {A B : ℝ}
    (hFb : ∀ t, |F t| ≤ A) (hHb : ∀ t, |H t| ≤ B) :
    twoRateInverse r s (fun t => F t - H t) =
      fun t => twoRateInverse r s F t - twoRateInverse r s H t := by
  funext t
  have hFL := (exp_source_integrable hr hF hFb t).1
  have hFR := (exp_source_integrable hs hF hFb t).2
  have hHL := (exp_source_integrable hr hH hHb t).1
  have hHR := (exp_source_integrable hs hH hHb t).2
  unfold twoRateInverse leftTail rightTail
  simp_rw [mul_sub]
  rw [integral_sub hFL hHL, integral_sub hFR hHR]
  ring

def twoRateResolvent (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (twoRateInverse r s F)
    (twoRateInverse_differentiable_equation hr hs F.continuous
      (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t)).1.continuous
    (‖F‖ / (r * s))
    (fun t => by simpa only [Real.norm_eq_abs] using
      twoRateInverse_bound hr hs (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t) t)

theorem twoRateResolvent_norm_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (F : ℝ →ᵇ ℝ) :
    ‖twoRateResolvent r s hr hs F‖ ≤ ‖F‖ / (r * s) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖twoRateInverse r s F t‖ ≤ ‖F‖ / (r * s)
  simpa only [Real.norm_eq_abs] using
    twoRateInverse_bound hr hs (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t) t

theorem twoRateResolvent_sub {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (F H : ℝ →ᵇ ℝ) :
    twoRateResolvent r s hr hs (F - H) =
      twoRateResolvent r s hr hs F - twoRateResolvent r s hr hs H := by
  apply BoundedContinuousFunction.ext
  intro t
  exact congrFun (twoRateInverse_sub hr hs F.continuous H.continuous
    (fun t => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm t)
    (fun t => by simpa only [Real.norm_eq_abs] using H.norm_coe_le_norm t)) t

theorem twoRateResolvent_dist_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (F H : ℝ →ᵇ ℝ) :
    dist (twoRateResolvent r s hr hs F) (twoRateResolvent r s hr hs H) ≤ dist F H / (r * s) := by
  rw [dist_eq_norm, dist_eq_norm, ← twoRateResolvent_sub hr hs]
  exact twoRateResolvent_norm_le hr hs (F - H)

#print axioms twoRateInverse_differentiable_equation
#print axioms twoRateResolvent_dist_le

end Yamabe3.Analysis.Delaunay
