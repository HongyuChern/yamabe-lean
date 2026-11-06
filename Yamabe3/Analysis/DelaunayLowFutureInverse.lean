import Yamabe3.Analysis.FuturePotentialInverse

/-!
# Neck-independent low-mode inverse for strong future decay

For every numerical mode 0 <= mu <= 2, the Delaunay Jacobi coefficient has
absolute value at most 7/2. The actual future-tail contraction consequently
has gap k^2-7/2, uniformly over all genuine necks. Both the solution and its
first derivative satisfy an explicit bound. No entrance value is imposed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem lowJacobiCoefficient_abs_le {v : ℝ → ℝ}
    (hv : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ₂ : μ ≤ 2) (t : ℝ) :
    |1 / 4 + μ - (15 / 4) * v t ^ 4| ≤ 7 / 2 := by
  have hb := pow_le_one₀ (hv t).1 (hv t).2 (n := 4)
  have hn := pow_nonneg (hv t).1 4
  rw [abs_le]
  constructor <;> nlinarith

/-- An actual smooth low-mode solution for a strongly decaying smooth
source. All constants are independent of the neck and of the source. -/
theorem exists_strong_future_low_mode_solution {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvbound : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {μ k : ℝ}
    (hμ₀ : 0 ≤ μ) (hμ₂ : μ ≤ 2) (hk : 0 < k) (hgap : 7 / 2 < k ^ 2)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {A : ℝ} (hA : 0 ≤ A)
    (hFb : ∀ t, |F t| ≤ A * Real.exp (-k * t)) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ t, modelJacobi v μ u t = F t) ∧
      (∀ t, |u t| ≤ (A / (k ^ 2 - 7 / 2)) * Real.exp (-k * t)) ∧
      (∀ t, |deriv u t| ≤ (k * A / (k ^ 2 - 7 / 2)) * Real.exp (-k * t)) := by
  let afun : ℝ → ℝ := fun t => 1 / 4 + μ - (15 / 4) * v t ^ 4
  have has : ContDiff ℝ ∞ afun := contDiff_const.sub (contDiff_const.mul (hv.pow 4))
  have hab (t : ℝ) : ‖afun t‖ ≤ 7 / 2 := by
    simpa only [Real.norm_eq_abs] using lowJacobiCoefficient_abs_le hvbound hμ₀ hμ₂ t
  let a : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup afun has.continuous (7 / 2) hab
  have han : ‖a‖ ≤ 7 / 2 := (BoundedContinuousFunction.norm_le (by norm_num)).mpr hab
  have hag : ‖a‖ < k ^ 2 := han.trans_lt hgap
  let H : ℝ → ℝ := fun t => Real.exp (k * t) * F t
  have hHs : ContDiff ℝ ∞ H :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hF
  have hHb (t : ℝ) : |H t| ≤ A := by
    dsimp [H]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (k * t) * (A * Real.exp (-k * t)) :=
        mul_le_mul_of_nonneg_left (hFb t) (Real.exp_pos _).le
      _ = A * Real.exp (k * t + -k * t) := by rw [Real.exp_add]; ring
      _ = A := by rw [show k * t + -k * t = 0 by ring, Real.exp_zero, mul_one]
  let Hb : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup H hHs.continuous A
    (fun t => by simpa only [Real.norm_eq_abs] using hHb t)
  have hHn : ‖Hb‖ ≤ A := by
    apply (BoundedContinuousFunction.norm_le hA).mpr
    intro t
    change ‖H t‖ ≤ A
    simpa only [Real.norm_eq_abs] using hHb t
  let w := futurePotentialInverse k hk a hag Hb
  have hws := futurePotentialInverse_contDiff hk a hag Hb has hHs
  have hwe := futurePotentialInverse_equation hk a hag Hb
  have hden : 0 < k ^ 2 - 7 / 2 := sub_pos.mpr hgap
  have hn : ‖Hb‖ / (k ^ 2 - ‖a‖) ≤ A / (k ^ 2 - 7 / 2) := by
    calc
      _ ≤ ‖Hb‖ / (k ^ 2 - 7 / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hden (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hHn hden.le
  refine ⟨fun t => Real.exp (-k * t) * w t,
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hws, ?_, ?_, ?_⟩
  · intro t
    unfold modelJacobi
    rw [exponential_conjugate_second_deriv hws]
    have he := hwe.2.2.2 t
    change deriv (deriv (fun t => w t)) t =
      2 * k * deriv (fun t => w t) t - k ^ 2 * w t + H t +
        (1 / 4 + μ - (15 / 4) * v t ^ 4) * w t at he
    rw [he]
    calc
      _ = Real.exp (-k * t) * H t := by ring
      _ = Real.exp (-k * t + k * t) * F t := by dsimp [H]; rw [Real.exp_add]; ring
      _ = F t := by rw [show -k * t + k * t = 0 by ring, Real.exp_zero, one_mul]
  · intro t
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-k * t) * ‖w‖ := mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using w.norm_coe_le_norm t) (Real.exp_pos _).le
      _ ≤ Real.exp (-k * t) * (A / (k ^ 2 - 7 / 2)) :=
        mul_le_mul_of_nonneg_left ((futurePotentialInverse_norm_le hk a hag Hb).trans hn)
          (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · intro t
    calc
      _ ≤ (k * ‖Hb‖ / (k ^ 2 - ‖a‖)) * Real.exp (-k * t) :=
        futurePotentialInverse_weighted_deriv_bound hk a hag Hb t
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hn hk.le

/-- The periodic model is genuinely constructed; the future inverse is
uniform over its neck and over both numerical low angular modes. -/
theorem exists_delaunay_strong_future_low_inverse {ε e : ℝ}
    (hε : 0 < ε) (he : 0 < e) (hsmall : ε ^ 2 * e < 3 / 8) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, ε * Real.sqrt e ≤ v t ∧ v t < 1) ∧
      (∀ t, deriv (deriv v) t = radialForce (v t)) ∧
      ∀ (μ k : ℝ), 0 ≤ μ → μ ≤ 2 → 0 < k → 7 / 2 < k ^ 2 →
        ∀ (F : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ F → 0 ≤ A →
          (∀ t, |F t| ≤ A * Real.exp (-k * t)) →
          ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
            (∀ t, modelJacobi v μ u t = F t) ∧
            (∀ t, |u t| ≤ (A / (k ^ 2 - 7 / 2)) * Real.exp (-k * t)) ∧
            (∀ t, |deriv u t| ≤ (k * A / (k ^ 2 - 7 / 2)) * Real.exp (-k * t)) := by
  obtain ⟨η, v, T, hη, _, hηlow, _, hT, hs, hp, hb, _, _, _, hode, _, _, _⟩ :=
    exists_delaunay_energy_parameters hε he hsmall
  refine ⟨v, T, hT, hs, hp, fun t => ⟨hηlow.trans (hb t).1, (hb t).2⟩, hode, ?_⟩
  intro μ k hμ₀ hμ₂ hk hgap F A hF hA hFb
  exact exists_strong_future_low_mode_solution hs
    (fun t => ⟨hη.le.trans (hb t).1, (hb t).2.le⟩) hμ₀ hμ₂ hk hgap hF hA hFb

end Yamabe3.Analysis.Delaunay
