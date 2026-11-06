import Yamabe3.Analysis.ExponentialFutureInverse
import Yamabe3.Analysis.DelaunayWeightedInverse

/-!
# A genuine future inverse with a small bounded potential

The complete bounded-continuous fixed point solves (D-k)^2 w = F + a w.
All integrals are the actual future tails already differentiated in
ExponentialFutureInverse. The displayed gap is k^2 - ||a||.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def futurePotentialIteration (k : ℝ) (hk : 0 < k) (a F w : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  doubleFutureResolvent k hk (F + a * w)

theorem futurePotentialIteration_contracting {k : ℝ} (hk : 0 < k)
    (a F : ℝ →ᵇ ℝ) (ha : ‖a‖ < k ^ 2) :
    ContractingWith ⟨‖a‖ / k ^ 2, div_nonneg (norm_nonneg _) (sq_nonneg _)⟩
      (futurePotentialIteration k hk a F) := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  refine ⟨(div_lt_one hk2).mpr ha, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖doubleFutureResolvent k hk (F + a * u) -
    doubleFutureResolvent k hk (F + a * w)‖ ≤ _
  rw [← doubleFutureResolvent_sub hk]
  have he : (F + a * u) - (F + a * w) = a * (u - w) := by ring
  rw [he]
  change ‖doubleFutureResolvent k hk (a * (u - w))‖ ≤
    (‖a‖ / k ^ 2) * ‖u - w‖
  calc
    _ ≤ ‖a * (u - w)‖ / k ^ 2 := doubleFutureResolvent_norm_le hk _
    _ ≤ (‖a‖ * ‖u - w‖) / k ^ 2 :=
      div_le_div_of_nonneg_right (norm_mul_le _ _) hk2.le
    _ = _ := by ring

/-- The actual future fixed point, with no Cauchy or inverse input. -/
def futurePotentialInverse (k : ℝ) (hk : 0 < k) (a : ℝ →ᵇ ℝ)
    (ha : ‖a‖ < k ^ 2) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  (futurePotentialIteration_contracting hk a F ha).fixedPoint
    (futurePotentialIteration k hk a F)

theorem futurePotentialInverse_fixed {k : ℝ} (hk : 0 < k) (a : ℝ →ᵇ ℝ)
    (ha : ‖a‖ < k ^ 2) (F : ℝ →ᵇ ℝ) :
    doubleFutureResolvent k hk (F + a * futurePotentialInverse k hk a ha F) =
      futurePotentialInverse k hk a ha F :=
  (futurePotentialIteration_contracting hk a F ha).fixedPoint_isFixedPt

theorem futurePotentialInverse_norm_le {k : ℝ} (hk : 0 < k) (a : ℝ →ᵇ ℝ)
    (ha : ‖a‖ < k ^ 2) (F : ℝ →ᵇ ℝ) :
    ‖futurePotentialInverse k hk a ha F‖ ≤ ‖F‖ / (k ^ 2 - ‖a‖) := by
  let u := futurePotentialInverse k hk a ha F
  have he := futurePotentialInverse_fixed hk a ha F
  have hn : ‖u‖ ≤ (‖F‖ + ‖a‖ * ‖u‖) / k ^ 2 := by
    calc
      ‖u‖ = ‖doubleFutureResolvent k hk (F + a * u)‖ := congrArg norm he.symm
      _ ≤ ‖F + a * u‖ / k ^ 2 := doubleFutureResolvent_norm_le hk _
      _ ≤ (‖F‖ + ‖a‖ * ‖u‖) / k ^ 2 :=
        div_le_div_of_nonneg_right
          ((norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))) (sq_nonneg _)
  have hm := (le_div_iff₀ (sq_pos_of_pos hk)).mp hn
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  dsimp only [u] at hm ⊢
  nlinarith

theorem futurePotentialInverse_equation {k : ℝ} (hk : 0 < k) (a : ℝ →ᵇ ℝ)
    (ha : ‖a‖ < k ^ 2) (F : ℝ →ᵇ ℝ) :
    let u := futurePotentialInverse k hk a ha F
    Differentiable ℝ (fun t => u t) ∧ Differentiable ℝ (deriv (fun t => u t)) ∧
      (∀ t, deriv (fun s => u s) t = k * u t - futureResolvent k hk (F + a * u) t) ∧
      ∀ t, deriv (deriv (fun s => u s)) t =
        2 * k * deriv (fun s => u s) t - k ^ 2 * u t + F t + a t * u t := by
  dsimp only
  let u := futurePotentialInverse k hk a ha F
  have he : (fun t => doubleFutureResolvent k hk (F + a * u) t) = fun t => u t := by
    funext t
    exact congrArg (fun w : ℝ →ᵇ ℝ => w t) (futurePotentialInverse_fixed hk a ha F)
  have h := doubleFutureResolvent_equation hk (F + a * u)
  dsimp only at h
  rw [he] at h
  refine ⟨h.1, h.2.1, ?_, fun t => ?_⟩
  · intro t
    simpa only [congrFun he t] using h.2.2.1 t
  have ht := h.2.2.2 t
  rw [congrFun he t] at ht
  change deriv (deriv (fun t => u t)) t =
    2 * k * deriv (fun t => u t) t - k ^ 2 * u t + (F t + a t * u t) at ht
  simpa only [add_assoc] using ht

theorem futurePotentialInverse_contDiff {k : ℝ} (hk : 0 < k) (a : ℝ →ᵇ ℝ)
    (ha : ‖a‖ < k ^ 2) (F : ℝ →ᵇ ℝ)
    (has : ContDiff ℝ ∞ (fun t => a t)) (hFs : ContDiff ℝ ∞ (fun t => F t)) :
    ContDiff ℝ ∞ (fun t => futurePotentialInverse k hk a ha F t) := by
  have h := futurePotentialInverse_equation hk a ha F
  apply contDiff_of_second_order_linear_drift h.1 h.2.1 has.neg hFs
    (a := -k ^ 2) (b := 2 * k)
  intro t
  simpa only [Pi.neg_apply, neg_mul, neg_neg, sub_neg_eq_add, sub_eq_add_neg] using h.2.2.2 t

/-- After undoing the exponential weight, the first derivative has one
future tail, giving a uniform sharp factor k/(k^2-||a||). -/
theorem futurePotentialInverse_weighted_deriv_bound {k : ℝ} (hk : 0 < k)
    (a : ℝ →ᵇ ℝ) (ha : ‖a‖ < k ^ 2) (F : ℝ →ᵇ ℝ) (t : ℝ) :
    |deriv (fun s => Real.exp (-k * s) * futurePotentialInverse k hk a ha F s) t| ≤
      (k * ‖F‖ / (k ^ 2 - ‖a‖)) * Real.exp (-k * t) := by
  let w := futurePotentialInverse k hk a ha F
  have h := futurePotentialInverse_equation hk a ha F
  have he : HasDerivAt (fun s : ℝ => Real.exp (-k * s))
      (-k * Real.exp (-k * t)) t := by
    apply (((hasDerivAt_id t).const_mul (-k)).exp).congr_deriv
    simp only [id_eq]
    ring
  have hd : HasDerivAt (fun s => Real.exp (-k * s) * w s)
      (-k * Real.exp (-k * t) * w t +
        Real.exp (-k * t) * deriv (fun s => w s) t) t :=
    he.mul (h.1 t).hasDerivAt
  change |deriv (fun s => Real.exp (-k * s) * w s) t| ≤ _
  rw [hd.deriv, h.2.2.1]
  have halg : -k * Real.exp (-k * t) * w t +
      Real.exp (-k * t) * (k * w t - futureResolvent k hk (F + a * w) t) =
        -Real.exp (-k * t) * futureResolvent k hk (F + a * w) t := by ring
  rw [halg, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
  have hgap : 0 < k ^ 2 - ‖a‖ := sub_pos.mpr ha
  have hn : ‖F + a * w‖ ≤ ‖F‖ + ‖a‖ * (‖F‖ / (k ^ 2 - ‖a‖)) :=
    (norm_add_le _ _).trans (add_le_add le_rfl
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (futurePotentialInverse_norm_le hk a ha F) (norm_nonneg _))))
  have hp : |futureResolvent k hk (F + a * w) t| ≤
      ‖futureResolvent k hk (F + a * w)‖ := by
    simpa only [Real.norm_eq_abs] using
      (futureResolvent k hk (F + a * w)).norm_coe_le_norm t
  calc
    _ ≤ Real.exp (-k * t) * (‖F + a * w‖ / k) :=
      mul_le_mul_of_nonneg_left
        (hp.trans (futureResolvent_norm_le hk _)) (Real.exp_pos _).le
    _ ≤ Real.exp (-k * t) * ((‖F‖ + ‖a‖ * (‖F‖ / (k ^ 2 - ‖a‖))) / k) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hk.le) (Real.exp_pos _).le
    _ = _ := by field_simp; ring

end Yamabe3.Analysis.Delaunay
