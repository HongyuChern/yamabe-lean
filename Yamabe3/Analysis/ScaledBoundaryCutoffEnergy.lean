import Yamabe3.Analysis.ScaledIntervalTrace
import Mathlib.Tactic.Ring

/-!
# Actual boundary-layer energy controlled by one endpoint trace

This is the radial estimate for removing a zero-trace collar. The endpoint
value is retained explicitly before completion. The constants are coarse
but uniform: on a collar of width 2 delta the squared cutoff cost is
bounded by 4/delta times the endpoint square plus 16 times the derivative
energy in that same collar. No restriction of an ambient AE identity to
the boundary is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology

namespace Yamabe3.Analysis.SpherePolar

/-- A genuine FTC estimate retaining the actual endpoint value. The
factor four in the derivative term is a proved uniform upper bound. -/
theorem integral_sq_le_endpoint_and_derivative_energy
    {a b : ℝ} (hab : a < b) {f df : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t) :
    (∫ t in Icc a b, f t ^ 2) ≤
      2 * (b - a) * f a ^ 2 + 4 * (b - a) ^ 2 * ∫ t in Icc a b, df t ^ 2 := by
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  have h2L : 0 < 2 * L := by positivity
  let q : ℝ → ℝ := fun t => f t ^ 2 + (2 * L) ^ 2 * df t ^ 2
  let d : ℝ → ℝ := fun t => 2 * f t * df t
  have hfi : IntegrableOn (fun t => f t ^ 2) (Icc a b) :=
    (hf.pow 2).integrableOn_compact isCompact_Icc
  have hdfi : IntegrableOn (fun t => df t ^ 2) (Icc a b) :=
    (hdf.pow 2).integrableOn_compact isCompact_Icc
  have hqi : IntegrableOn q (Icc a b) :=
    hfi.add (hdfi.const_mul ((2 * L) ^ 2))
  have hdc : ContinuousOn d (Icc a b) := (continuousOn_const.mul hf).mul hdf
  have hdi : IntegrableOn (fun t => ‖d t‖) (Icc a b) :=
    hdc.norm.integrableOn_compact isCompact_Icc
  have hdq (t : ℝ) : ‖d t‖ ≤ (2 * L)⁻¹ * q t := by
    rw [← div_eq_inv_mul, le_div_iff₀ h2L, Real.norm_eq_abs]
    by_cases hp : 0 ≤ d t
    · rw [abs_of_nonneg hp]
      dsimp only [d, q]
      nlinarith only [sq_nonneg (f t - (2 * L) * df t)]
    · rw [abs_of_neg (lt_of_not_ge hp)]
      dsimp only [d, q]
      nlinarith only [sq_nonneg (f t + (2 * L) * df t)]
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      f s ^ 2 ≤ f a ^ 2 + (2 * L)⁻¹ * ∫ t in Icc a b, q t := by
    have hsub : uIcc a s ⊆ Icc a b := by
      intro t ht
      exact ⟨(le_min le_rfl hs.1).trans ht.1,
        ht.2.trans (max_le hab.le hs.2)⟩
    have hftc : (∫ t in a..s, d t) = f s ^ 2 - f a ^ 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => f t ^ 2) (f' := d)
      · intro t ht
        simpa only [d, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using!
          (hd t (hsub ht)).pow 2
      · exact (hdc.mono hsub).intervalIntegrable
    have hn : |f s ^ 2 - f a ^ 2| ≤ (2 * L)⁻¹ * ∫ t in Icc a b, q t := by
      calc
        _ = ‖∫ t in a..s, d t‖ := by rw [hftc, Real.norm_eq_abs]
        _ ≤ ∫ t in uIoc a s, ‖d t‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ t in Icc a b, ‖d t‖ :=
          setIntegral_mono_set hdi (Eventually.of_forall fun _ => norm_nonneg _)
            (Eventually.of_forall fun t ht => hsub (uIoc_subset_uIcc ht))
        _ ≤ ∫ t in Icc a b, (2 * L)⁻¹ * q t :=
          setIntegral_mono_on hdi (hqi.const_mul _) measurableSet_Icc (fun t _ => hdq t)
        _ = _ := integral_const_mul _ _
    have hle := (le_abs_self (f s ^ 2 - f a ^ 2)).trans hn
    linarith only [hle]
  have hconst : IntegrableOn
      (fun _ : ℝ => f a ^ 2 + (2 * L)⁻¹ * ∫ t in Icc a b, q t) (Icc a b) :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ => f a ^ 2 + (2 * L)⁻¹ * ∫ t in Icc a b, q t)
      (Icc a b)).integrableOn_compact isCompact_Icc
  have havg := setIntegral_mono_on hfi hconst measurableSet_Icc hpoint
  have hq : (∫ t in Icc a b, q t) =
      (∫ t in Icc a b, f t ^ 2) + (2 * L) ^ 2 * ∫ t in Icc a b, df t ^ 2 := by
    rw [show q = fun t => f t ^ 2 + (2 * L) ^ 2 * df t ^ 2 by rfl,
      integral_add hfi (hdfi.const_mul _), integral_const_mul]
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
    Real.volume_real_Icc_of_le hab.le, hq] at havg
  change (∫ t in Icc a b, f t ^ 2) ≤
    L * (f a ^ 2 + (2 * L)⁻¹ *
      ((∫ t in Icc a b, f t ^ 2) + (2 * L) ^ 2 * ∫ t in Icc a b, df t ^ 2)) at havg
  have halg : L * (f a ^ 2 + (2 * L)⁻¹ *
      ((∫ t in Icc a b, f t ^ 2) + (2 * L) ^ 2 * ∫ t in Icc a b, df t ^ 2)) =
      L * f a ^ 2 + (∫ t in Icc a b, f t ^ 2) / 2 +
        2 * L ^ 2 * ∫ t in Icc a b, df t ^ 2 := by
    field_simp [hL.ne']
    <;> ring
  rw [halg] at havg
  change (∫ t in Icc a b, f t ^ 2) ≤
    2 * L * f a ^ 2 + 4 * L ^ 2 * ∫ t in Icc a b, df t ^ 2
  linarith only [havg]

/-- The actual squared cost of a cutoff with derivative of order delta^-1.
The trace term is kept until a genuine continuous trace limit makes it zero. -/
theorem scaled_boundary_layer_energy_le
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) {f df : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a (a + 2 * δ)))
    (hdf : ContinuousOn df (Icc a (a + 2 * δ)))
    (hd : ∀ t ∈ Icc a (a + 2 * δ), HasDerivAt f (df t) t) :
    δ⁻¹ ^ 2 * (∫ t in Icc a (a + 2 * δ), f t ^ 2) ≤
      (4 / δ) * f a ^ 2 + 16 * ∫ t in Icc a (a + 2 * δ), df t ^ 2 := by
  have h := integral_sq_le_endpoint_and_derivative_energy (by linarith : a < a + 2 * δ)
    hf hdf hd
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg δ⁻¹)
  calc
    _ ≤ δ⁻¹ ^ 2 * (2 * ((a + 2 * δ) - a) * f a ^ 2 +
        4 * ((a + 2 * δ) - a) ^ 2 * ∫ t in Icc a (a + 2 * δ), df t ^ 2) := hm
    _ = _ := by
      have hlen : a + 2 * δ - a = 2 * δ := by ring
      rw [hlen]
      generalize (∫ t in Icc a (a + 2 * δ), df t ^ 2) = J
      field_simp [hδ.ne']
      <;> ring

#print axioms integral_sq_le_endpoint_and_derivative_energy
#print axioms scaled_boundary_layer_energy_le

end Yamabe3.Analysis.SpherePolar
