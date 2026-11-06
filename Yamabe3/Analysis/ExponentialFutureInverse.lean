import Yamabe3.Analysis.ExponentialKernelInverse
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Actual future inverses for strong exponential weights

One normalized future tail has norm at most 1/k and solves a first-order
ODE. Composing it twice gives a true inverse of (D-k)^2 with norm 1/k^2.
This supplies neck-independent low-mode inverses for the high-order normal
coordinate remainder, without any entrance condition.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def futureTail (k : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (k * t) * rightTail (fun s => Real.exp (-k * s) * F s) t

theorem futureTail_bound {k : ℝ} (hk : 0 < k) {F : ℝ → ℝ} {A : ℝ}
    (hF : ∀ t, |F t| ≤ A) (t : ℝ) : |futureTail k F t| ≤ A / k := by
  rw [futureTail, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (k * t) * (A * Real.exp (-k * t) / k) :=
      mul_le_mul_of_nonneg_left (exp_tail_bounds hk hF t).2 (Real.exp_pos _).le
    _ = _ := by
      have he : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
        rw [← Real.exp_add, show k * t + -k * t = 0 by ring, Real.exp_zero]
      calc
        _ = A / k * (Real.exp (k * t) * Real.exp (-k * t)) := by ring
        _ = _ := by rw [he, mul_one]

theorem futureTail_hasDerivAt {k : ℝ} (hk : 0 < k) {F : ℝ → ℝ}
    (hF : Continuous F) {A : ℝ} (hb : ∀ t, |F t| ≤ A) (t : ℝ) :
    HasDerivAt (futureTail k F) (k * futureTail k F t - F t) t := by
  have hExp : Continuous (fun s : ℝ => Real.exp (-k * s) * F s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF
  have hR : HasDerivAt (rightTail (fun s : ℝ => Real.exp (-k * s) * F s))
      (-(Real.exp (-k * t) * F t)) t :=
    rightTail_hasDerivAt hExp (fun s => (exp_source_integrable hk hF hb s).2) t
  have he : HasDerivAt (fun y : ℝ => Real.exp (k * y)) (k * Real.exp (k * t)) t := by
    apply (((hasDerivAt_id t).const_mul k).exp).congr_deriv
    simp only [id_eq]
    ring
  apply (he.mul hR).congr_deriv
  have hprod : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
    rw [← Real.exp_add, show k * t + -k * t = 0 by ring, Real.exp_zero]
  dsimp [futureTail]
  nlinarith [congrArg (fun a : ℝ => a * F t) hprod]

def futureResolvent (k : ℝ) (hk : 0 < k) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (futureTail k F)
    (continuous_iff_continuousAt.mpr (fun t => (futureTail_hasDerivAt hk F.continuous
      (fun s => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm s) t).continuousAt))
    (‖F‖ / k) (fun t => by
      simpa only [Real.norm_eq_abs] using
        (futureTail_bound hk (fun s => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm s) t))

theorem futureResolvent_norm_le {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ ℝ) :
    ‖futureResolvent k hk F‖ ≤ ‖F‖ / k := by
  apply (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg _) hk.le)).mpr
  intro t
  change ‖futureTail k F t‖ ≤ ‖F‖ / k
  exact (by simpa only [Real.norm_eq_abs] using
    futureTail_bound hk (fun s => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm s) t)

theorem futureResolvent_hasDerivAt {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ ℝ) (t : ℝ) :
    HasDerivAt (fun s => futureResolvent k hk F s) (k * futureResolvent k hk F t - F t) t :=
  futureTail_hasDerivAt hk F.continuous
    (fun s => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm s) t

theorem futureResolvent_sub {k : ℝ} (hk : 0 < k) (F H : ℝ →ᵇ ℝ) :
    futureResolvent k hk (F - H) = futureResolvent k hk F - futureResolvent k hk H := by
  apply BoundedContinuousFunction.ext
  intro t
  change futureTail k (fun s => F s - H s) t = futureTail k F t - futureTail k H t
  unfold futureTail rightTail
  simp_rw [mul_sub]
  rw [integral_sub
    (exp_source_integrable hk F.continuous (fun s => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm s) t).2
    (exp_source_integrable hk H.continuous (fun s => by simpa only [Real.norm_eq_abs] using H.norm_coe_le_norm s) t).2]
  ring

def doubleFutureResolvent (k : ℝ) (hk : 0 < k) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  futureResolvent k hk (futureResolvent k hk F)

theorem doubleFutureResolvent_norm_le {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ ℝ) :
    ‖doubleFutureResolvent k hk F‖ ≤ ‖F‖ / k ^ 2 := by
  calc
    _ ≤ ‖futureResolvent k hk F‖ / k := futureResolvent_norm_le hk _
    _ ≤ (‖F‖ / k) / k := div_le_div_of_nonneg_right (futureResolvent_norm_le hk F) hk.le
    _ = _ := by ring

theorem doubleFutureResolvent_sub {k : ℝ} (hk : 0 < k) (F H : ℝ →ᵇ ℝ) :
    doubleFutureResolvent k hk (F - H) = doubleFutureResolvent k hk F - doubleFutureResolvent k hk H := by
  unfold doubleFutureResolvent
  rw [futureResolvent_sub hk, futureResolvent_sub hk]

theorem doubleFutureResolvent_equation {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ ℝ) :
    let u := fun t => doubleFutureResolvent k hk F t
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      (∀ t, deriv u t = k * u t - futureResolvent k hk F t) ∧
      ∀ t, deriv (deriv u) t = 2 * k * deriv u t - k ^ 2 * u t + F t := by
  dsimp only
  have hd (t : ℝ) := futureResolvent_hasDerivAt hk (futureResolvent k hk F) t
  have heq : deriv (fun t => doubleFutureResolvent k hk F t) =
      fun t => k * doubleFutureResolvent k hk F t - futureResolvent k hk F t :=
    funext fun t => (hd t).deriv
  have hd2 (t : ℝ) : HasDerivAt
      (fun s => k * doubleFutureResolvent k hk F s - futureResolvent k hk F s)
      (k * (k * doubleFutureResolvent k hk F t - futureResolvent k hk F t) -
        (k * futureResolvent k hk F t - F t)) t :=
    ((hd t).const_mul k).sub (futureResolvent_hasDerivAt hk F t)
  refine ⟨fun t => (hd t).differentiableAt, ?_, fun t => (hd t).deriv, ?_⟩
  · rw [heq]
    exact fun t => (hd2 t).differentiableAt
  · intro t
    rw [heq, (hd2 t).deriv]
    ring

end Yamabe3.Analysis.Delaunay
