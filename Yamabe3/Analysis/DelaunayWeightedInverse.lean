import Yamabe3.Analysis.TwoRateKernelInverse
import Yamabe3.Analysis.DelaunayHighInverse

/-!
# Actual exponential-weighted scalar high-mode inverse

The two-rate kernel with positive rates is used in the complete
bounded-continuous space after conjugation by exp(delta*t). This yields a genuine weighted
solution operator, with all constants displayed and uniform in the neck.
Only the numerical scalar angular mode is treated here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def driftPotentialIteration (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (V F : ℝ →ᵇ ℝ) (u : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  twoRateResolvent r s hr hs (F - V * u)

theorem driftPotentialIteration_contracting {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (V F : ℝ →ᵇ ℝ) (hV : ‖V‖ < r * s) :
    ContractingWith ⟨‖V‖ / (r * s), by positivity⟩ (driftPotentialIteration r s hr hs V F) := by
  refine ⟨?_, ?_⟩
  · change ‖V‖ / (r * s) < 1
    exact (div_lt_one (mul_pos hr hs)).mpr hV
  · apply LipschitzWith.of_dist_le_mul
    intro u w
    change dist (twoRateResolvent r s hr hs (F - V * u))
      (twoRateResolvent r s hr hs (F - V * w)) ≤ (‖V‖ / (r * s)) * dist u w
    have hsource : dist (F - V * u) (F - V * w) ≤ ‖V‖ * dist u w := by
      rw [dist_eq_norm, dist_eq_norm]
      have heq : (F - V * u) - (F - V * w) = -(V * (u - w)) := by ring
      rw [heq, norm_neg]
      exact norm_mul_le _ _
    calc
      _ ≤ dist (F - V * u) (F - V * w) / (r * s) := twoRateResolvent_dist_le hr hs _ _
      _ ≤ (‖V‖ * dist u w) / (r * s) :=
        div_le_div_of_nonneg_right hsource (mul_pos hr hs).le
      _ = _ := by ring

def driftPotentialInverse (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < r * s) (F : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  (driftPotentialIteration_contracting hr hs V F hV).fixedPoint
    (driftPotentialIteration r s hr hs V F)

theorem driftPotentialInverse_fixed {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < r * s) (F : ℝ →ᵇ ℝ) :
    twoRateResolvent r s hr hs (F - V * driftPotentialInverse r s hr hs V hV F) =
      driftPotentialInverse r s hr hs V hV F :=
  (driftPotentialIteration_contracting hr hs V F hV).fixedPoint_isFixedPt

theorem driftPotentialInverse_differentiable_equation {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < r * s) (F : ℝ →ᵇ ℝ) :
    let u := driftPotentialInverse r s hr hs V hV F
    Differentiable ℝ (fun t => u t) ∧
      Differentiable ℝ (deriv (fun t => u t)) ∧
      ∀ t, deriv (deriv (fun t => u t)) t =
        (s - r) * deriv (fun t => u t) t + (r * s) * u t + F t - V t * u t := by
  dsimp only
  let u := driftPotentialInverse r s hr hs V hV F
  have hrep : twoRateInverse r s ((F - V * u : ℝ →ᵇ ℝ) : ℝ → ℝ) = (fun t => u t) := by
    funext t
    exact congrArg (fun H : ℝ →ᵇ ℝ => H t) (driftPotentialInverse_fixed hr hs V hV F)
  have h := twoRateInverse_differentiable_equation hr hs (F - V * u).continuous
    (fun t => by simpa only [Real.norm_eq_abs] using (F - V * u).norm_coe_le_norm t)
  rw [hrep] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have he := h.2.2 t
  change deriv (deriv (fun t => u t)) t =
    (s - r) * deriv (fun t => u t) t + (r * s) * u t + (F t - V t * u t) at he
  simpa only [add_sub_assoc] using he

theorem driftPotentialInverse_norm_bound {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < r * s) (F : ℝ →ᵇ ℝ) :
    ‖driftPotentialInverse r s hr hs V hV F‖ ≤ ‖F‖ / (r * s - ‖V‖) := by
  let u := driftPotentialInverse r s hr hs V hV F
  have heq := driftPotentialInverse_fixed hr hs V hV F
  have hn : ‖u‖ ≤ (‖F‖ + ‖V‖ * ‖u‖) / (r * s) := by
    calc
      ‖u‖ = ‖twoRateResolvent r s hr hs (F - V * u)‖ := congrArg norm heq.symm
      _ ≤ ‖F - V * u‖ / (r * s) := twoRateResolvent_norm_le hr hs _
      _ ≤ (‖F‖ + ‖V‖ * ‖u‖) / (r * s) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hr hs).le
        exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_mul_le V u))
  have hmul := (le_div_iff₀ (mul_pos hr hs)).mp hn
  apply (le_div_iff₀ (sub_pos.mpr hV)).mpr
  dsimp only [u] at hmul ⊢
  nlinarith

theorem contDiff_of_second_order_linear_drift {u V F : ℝ → ℝ} {a b : ℝ}
    (hu : Differentiable ℝ u) (hdu : Differentiable ℝ (deriv u))
    (hV : ContDiff ℝ ∞ V) (hF : ContDiff ℝ ∞ F)
    (heq : ∀ t, deriv (deriv u) t = b * deriv u t + a * u t + F t - V t * u t) :
    ContDiff ℝ ∞ u := by
  have hn : ∀ n : ℕ, ContDiff ℝ n u ∧ ContDiff ℝ n (deriv u) := by
    intro n
    induction n with
    | zero => exact ⟨contDiff_zero.mpr hu.continuous, contDiff_zero.mpr hdu.continuous⟩
    | succ n ih =>
      have hD2 : ContDiff ℝ n (deriv (deriv u)) := by
        have hf : deriv (deriv u) = fun t => b * deriv u t + a * u t + F t - V t * u t := funext heq
        rw [hf]
        exact (((contDiff_const.mul ih.2).add (contDiff_const.mul ih.1)).add
          (contDiff_infty.mp hF n)).sub ((contDiff_infty.mp hV n).mul ih.1)
      constructor
      · exact contDiff_succ_iff_deriv.mpr ⟨hu, by simp, ih.2⟩
      · exact contDiff_succ_iff_deriv.mpr ⟨hdu, by simp, hD2⟩
  exact contDiff_infty.mpr fun n => (hn n).1

theorem driftPotentialInverse_contDiff {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < r * s) (F : ℝ →ᵇ ℝ)
    (hVs : ContDiff ℝ ∞ (fun t => V t)) (hFs : ContDiff ℝ ∞ (fun t => F t)) :
    ContDiff ℝ ∞ (fun t => driftPotentialInverse r s hr hs V hV F t) := by
  have h := driftPotentialInverse_differentiable_equation hr hs V hV F
  exact contDiff_of_second_order_linear_drift h.1 h.2.1 hVs hFs h.2.2

theorem exponential_conjugate_second_deriv {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (δ t : ℝ) :
    deriv (deriv (fun y => Real.exp (δ * y) * u y)) t =
      Real.exp (δ * t) * (δ ^ 2 * u t + 2 * δ * deriv u t + deriv (deriv u) t) := by
  have hexp (y : ℝ) : HasDerivAt (fun z : ℝ => Real.exp (δ * z))
      (δ * Real.exp (δ * y)) y := by
    apply (((hasDerivAt_id y).const_mul δ).exp).congr_deriv
    simp only [id_eq]
    ring
  have hud (y : ℝ) := (hu.differentiable (by simp) y).hasDerivAt
  have hfirst (y : ℝ) : HasDerivAt (fun z => Real.exp (δ * z) * u z)
      (Real.exp (δ * y) * (δ * u y + deriv u y)) y := by
    apply ((hexp y).mul (hud y)).congr_deriv
    ring
  have hid : deriv (fun y => Real.exp (δ * y) * u y) =
      fun y => Real.exp (δ * y) * (δ * u y + deriv u y) := funext fun y => (hfirst y).deriv
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have h2 := (hexp t).mul (((hud t).const_mul δ).add
    ((hdu.differentiable (by simp) t).hasDerivAt))
  change HasDerivAt (fun y => Real.exp (δ * y) * (δ * u y + deriv u y))
    (δ * Real.exp (δ * t) * (δ * u t + deriv u t) +
      Real.exp (δ * t) * (δ * deriv u t + deriv (deriv u) t)) t at h2
  rw [hid, h2.deriv]
  ring

/-- A genuine exponential-weighted inverse of each numerical high angular
mode. The source may grow on one end of the line and decay on the other. -/
theorem exists_weighted_high_mode_solution {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvbound : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {eigenvalue δ : ℝ} (heigen : 6 ≤ eigenvalue)
    (hweight : δ ^ 2 < eigenvalue - 7 / 2) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {A : ℝ} (hA : 0 ≤ A) (hFbound : ∀ t, |F t| ≤ A * Real.exp (δ * t)) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ t, modelJacobi v eigenvalue u t = F t) ∧
      (∀ t, |u t| ≤ (A / (eigenvalue - 7 / 2 - δ ^ 2)) * Real.exp (δ * t)) := by
  let k : ℝ := Real.sqrt (eigenvalue + 1 / 4)
  have hk : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hk2 : k ^ 2 = eigenvalue + 1 / 4 := Real.sq_sqrt (by linarith)
  have hδk : -k < δ ∧ δ < k := abs_lt_of_sq_lt_sq' (by rw [hk2]; linarith) hk.le
  let r := k + δ
  let s := k - δ
  have hr : 0 < r := by dsimp [r]; linarith [hδk.1]
  have hs : 0 < s := sub_pos.mpr hδk.2
  have hrs : r * s = eigenvalue + 1 / 4 - δ ^ 2 := by dsimp [r, s]; nlinarith [hk2]
  have hsr : s - r = -2 * δ := by dsimp [r, s]; ring
  let Vfun : ℝ → ℝ := fun t => (15 / 4) * v t ^ 4
  have hVs : ContDiff ℝ ∞ Vfun := contDiff_const.mul (hv.pow 4)
  have hVbound (t : ℝ) : ‖Vfun t‖ ≤ 15 / 4 := by
    have hp : v t ^ 4 ≤ 1 := pow_le_one₀ (hvbound t).1 (hvbound t).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [Vfun]; positivity)]
    dsimp [Vfun]
    linarith
  let V : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    Vfun hVs.continuous (15 / 4) hVbound
  have hVnorm : ‖V‖ ≤ 15 / 4 := (BoundedContinuousFunction.norm_le (by norm_num)).mpr hVbound
  have hVgap : ‖V‖ < r * s := by rw [hrs]; linarith
  let H : ℝ → ℝ := fun t => Real.exp (-δ * t) * F t
  have hHs : ContDiff ℝ ∞ H :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hF
  have hHbound (t : ℝ) : |H t| ≤ A := by
    change |Real.exp (-δ * t) * F t| ≤ A
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-δ * t) * (A * Real.exp (δ * t)) :=
        mul_le_mul_of_nonneg_left (hFbound t) (Real.exp_pos _).le
      _ = A * Real.exp (-δ * t + δ * t) := by rw [Real.exp_add]; ring
      _ = A := by rw [show -δ * t + δ * t = 0 by ring, Real.exp_zero, mul_one]
  let Hb : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup H hHs.continuous A
    (fun t => by simpa only [Real.norm_eq_abs] using hHbound t)
  have hHnorm : ‖Hb‖ ≤ A := by
    apply (BoundedContinuousFunction.norm_le hA).mpr
    intro t
    change ‖H t‖ ≤ A
    simpa only [Real.norm_eq_abs] using hHbound t
  let w := driftPotentialInverse r s hr hs V hVgap Hb
  have hws : ContDiff ℝ ∞ (fun t => w t) := driftPotentialInverse_contDiff hr hs V hVgap Hb hVs hHs
  have hweq := driftPotentialInverse_differentiable_equation hr hs V hVgap Hb
  have hden : 0 < eigenvalue - 7 / 2 - δ ^ 2 := sub_pos.mpr hweight
  have hwBound (t : ℝ) : |w t| ≤ A / (eigenvalue - 7 / 2 - δ ^ 2) := by
    calc
      |w t| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using w.norm_coe_le_norm t
      _ ≤ ‖Hb‖ / (r * s - ‖V‖) := driftPotentialInverse_norm_bound hr hs V hVgap Hb
      _ ≤ ‖Hb‖ / (eigenvalue - 7 / 2 - δ ^ 2) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) hden
        rw [hrs]
        linarith
      _ ≤ A / (eigenvalue - 7 / 2 - δ ^ 2) := div_le_div_of_nonneg_right hHnorm hden.le
  refine ⟨fun t => Real.exp (δ * t) * w t,
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hws, ?_, ?_⟩
  · intro t
    have he := hweq.2.2 t
    change deriv (deriv (fun t => w t)) t = (s - r) * deriv (fun t => w t) t +
      (r * s) * w t + H t - (15 / 4) * v t ^ 4 * w t at he
    unfold modelJacobi
    rw [exponential_conjugate_second_deriv hws, he, hrs, hsr]
    calc
      _ = Real.exp (δ * t) * H t := by ring
      _ = Real.exp (δ * t + -δ * t) * F t := by dsimp [H]; rw [Real.exp_add]; ring
      _ = F t := by rw [show δ * t + -δ * t = 0 by ring, Real.exp_zero, one_mul]
  · intro t
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (δ * t) * (A / (eigenvalue - 7 / 2 - δ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hwBound t) (Real.exp_pos (δ * t)).le
      _ = _ := mul_comm _ _

theorem exists_delaunay_weighted_high_mode_inverse {ε e : ℝ}
    (hε : 0 < ε) (he : 0 < e) (hsmall : ε ^ 2 * e < 3 / 8) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, ε * Real.sqrt e ≤ v t ∧ v t < 1) ∧
      (∀ t, deriv (deriv v) t = radialForce (v t)) ∧
      ∀ (eigenvalue δ : ℝ), 6 ≤ eigenvalue → δ ^ 2 < eigenvalue - 7 / 2 →
        ∀ (F : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ F → 0 ≤ A →
          (∀ t, |F t| ≤ A * Real.exp (δ * t)) →
          ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
            (∀ t, modelJacobi v eigenvalue u t = F t) ∧
            (∀ t, |u t| ≤ (A / (eigenvalue - 7 / 2 - δ ^ 2)) * Real.exp (δ * t)) := by
  obtain ⟨η, v, T, hη, _, hηlow, _, hT, hs, hp, hb, _, _, _, hode, _, _, _⟩ :=
    exists_delaunay_energy_parameters hε he hsmall
  refine ⟨v, T, hT, hs, hp, fun t => ⟨hηlow.trans (hb t).1, (hb t).2⟩, hode, ?_⟩
  intro eigenvalue δ heigen hweight F A hF hA hFb
  exact exists_weighted_high_mode_solution hs
    (fun t => ⟨hη.le.trans (hb t).1, (hb t).2.le⟩) heigen hweight hF hA hFb

#print axioms driftPotentialInverse_differentiable_equation
#print axioms exists_delaunay_weighted_high_mode_inverse

end Yamabe3.Analysis.Delaunay
