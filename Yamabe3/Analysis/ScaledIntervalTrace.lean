import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# A scale-covariant one-dimensional value trace

The interval length weights the derivative term.  This is the input for
the physical sphere estimate whose constant remains fixed as the radius
tends to zero.  All derivatives and integrals are literal real ones.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology

namespace Yamabe3.Analysis.SpherePolar

theorem sq_apply_le_scaled_interval_energy {a b r : ℝ} (hab : a < b)
    (hr : r ∈ Icc a b) {f df : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t) :
    f r ^ 2 ≤ (2 / (b - a)) *
      ∫ t in Icc a b, f t ^ 2 + (b - a) ^ 2 * df t ^ 2 := by
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  let q : ℝ → ℝ := fun t => f t ^ 2 + L ^ 2 * df t ^ 2
  let d : ℝ → ℝ := fun t => 2 * f t * df t
  have hqc : ContinuousOn q (Icc a b) :=
    (hf.pow 2).add (continuousOn_const.mul (hdf.pow 2))
  have hdc : ContinuousOn d (Icc a b) := (continuousOn_const.mul hf).mul hdf
  have hqi : IntegrableOn q (Icc a b) := hqc.integrableOn_compact isCompact_Icc
  have hdi : IntegrableOn (fun t => ‖d t‖) (Icc a b) :=
    hdc.norm.integrableOn_compact isCompact_Icc
  have hdq (t : ℝ) : ‖d t‖ ≤ L⁻¹ * q t := by
    rw [← div_eq_inv_mul, le_div_iff₀ hL, Real.norm_eq_abs]
    by_cases hdpos : 0 ≤ d t
    · rw [abs_of_nonneg hdpos]
      dsimp only [d, q]
      nlinarith only [sq_nonneg (f t - L * df t)]
    · rw [abs_of_neg (lt_of_not_ge hdpos)]
      dsimp only [d, q]
      nlinarith only [sq_nonneg (f t + L * df t)]
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      f r ^ 2 ≤ f s ^ 2 + L⁻¹ * ∫ t in Icc a b, q t := by
    have hsub : uIcc s r ⊆ Icc a b := by
      intro t ht
      exact ⟨(le_min hs.1 hr.1).trans ht.1, ht.2.trans (max_le hs.2 hr.2)⟩
    have hftc : (∫ t in s..r, d t) = f r ^ 2 - f s ^ 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => f t ^ 2) (f' := d)
      · intro t ht
        simpa only [d, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using!
          (hd t (hsub ht)).pow 2
      · exact (hdc.mono hsub).intervalIntegrable
    have hnorm : |f r ^ 2 - f s ^ 2| ≤ L⁻¹ * ∫ t in Icc a b, q t := by
      calc
        _ = ‖∫ t in s..r, d t‖ := by rw [hftc, Real.norm_eq_abs]
        _ ≤ ∫ t in uIoc s r, ‖d t‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ t in Icc a b, ‖d t‖ :=
          setIntegral_mono_set hdi (Eventually.of_forall fun _ => norm_nonneg _)
            (Eventually.of_forall fun t ht => hsub (uIoc_subset_uIcc ht))
        _ ≤ ∫ t in Icc a b, L⁻¹ * q t :=
          setIntegral_mono_on hdi (hqi.const_mul _) measurableSet_Icc (fun t _ => hdq t)
        _ = _ := integral_const_mul _ _
    have hle := (le_abs_self (f r ^ 2 - f s ^ 2)).trans hnorm
    linarith only [hle]
  have hfi : IntegrableOn (fun s => f s ^ 2) (Icc a b) :=
    (hf.pow 2).integrableOn_compact isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ => L⁻¹ * ∫ t in Icc a b, q t) (Icc a b) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => L⁻¹ * ∫ t in Icc a b, q t)
      (Icc a b)).integrableOn_compact isCompact_Icc
  have havg : L * f r ^ 2 ≤
      (∫ s in Icc a b, f s ^ 2) + L * (L⁻¹ * ∫ t in Icc a b, q t) := by
    have hi := setIntegral_mono_on
      ((continuousOn_const : ContinuousOn (fun _ : ℝ => f r ^ 2)
        (Icc a b)).integrableOn_compact isCompact_Icc)
      (hfi.add hconst) measurableSet_Icc hpoint
    simpa only [integral_add' hfi hconst, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, Real.volume_real_Icc_of_le hab.le, L] using hi
  have hfle : (∫ s in Icc a b, f s ^ 2) ≤ ∫ t in Icc a b, q t := by
    apply setIntegral_mono_on hfi hqi measurableSet_Icc
    intro t _
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg L) (sq_nonneg (df t)))
  have hcancel : L * (L⁻¹ * ∫ t in Icc a b, q t) = ∫ t in Icc a b, q t := by
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  rw [hcancel] at havg
  change f r ^ 2 ≤ (2 / L) * ∫ t in Icc a b, q t
  apply le_of_mul_le_mul_left (a := L) _ hL
  have hcancel₂ : L * ((2 / L) * ∫ t in Icc a b, q t) =
      2 * ∫ t in Icc a b, q t := by
    field_simp [hL.ne']
  rw [hcancel₂]
  linarith only [havg, hfle]

#print axioms sq_apply_le_scaled_interval_energy

end Yamabe3.Analysis.SpherePolar
