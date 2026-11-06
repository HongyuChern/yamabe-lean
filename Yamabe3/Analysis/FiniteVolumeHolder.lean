import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The finite-volume L6-to-L2 comparison

The norm and measure in this file are Mathlib's actual `eLpNorm` and `Measure`.
The comparison is an instance of Holder's inequality, with the exact volume
exponent `1/3`; its squared real form has exponent `2/3`.
No geometric inverse or coercivity estimate is assumed or asserted here.
-/

set_option autoImplicit false

open MeasureTheory

namespace Yamabe3.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v : X → ℝ}

/-- Holder comparison in the extended nonnegative real numbers. -/
theorem eLpNorm_two_le_six (hv : AEStronglyMeasurable v μ) :
    eLpNorm v 2 μ ≤ eLpNorm v 6 μ * (μ Set.univ) ^ (1 / 3 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := v) (μ := μ) (p := 2) (q := 6) (by norm_num) hv
  norm_num at h ⊢
  exact h

/-- An actual L6 function on a finite measure space is also in L2. -/
theorem memLp_two_of_six [IsFiniteMeasure μ] (hv : MemLp v 6 μ) : MemLp v 2 μ :=
  hv.mono_exponent (by norm_num)

/-- Finite real-valued seminorms, retaining their genuine measure dependence. -/
theorem toReal_eLpNorm_two_le_six [IsFiniteMeasure μ] (hv : MemLp v 6 μ) :
    (eLpNorm v 2 μ).toReal ≤
      (eLpNorm v 6 μ).toReal * (μ Set.univ).toReal ^ (1 / 3 : ℝ) := by
  have htop : eLpNorm v 6 μ * (μ Set.univ) ^ (1 / 3 : ℝ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top hv.eLpNorm_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have h := ENNReal.toReal_mono htop (eLpNorm_two_le_six hv.aestronglyMeasurable)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow] using h

/-- Squared L2-to-L6 Holder comparison in finite real seminorms. -/
theorem toReal_eLpNorm_two_sq_le_six [IsFiniteMeasure μ] (hv : MemLp v 6 μ) :
    (eLpNorm v 2 μ).toReal ^ 2 ≤
      (μ Set.univ).toReal ^ (2 / 3 : ℝ) * (eLpNorm v 6 μ).toReal ^ 2 := by
  have h := toReal_eLpNorm_two_le_six hv
  have hsq : (eLpNorm v 2 μ).toReal ^ 2 ≤
      ((eLpNorm v 6 μ).toReal * (μ Set.univ).toReal ^ (1 / 3 : ℝ)) ^ 2 := by
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm v 2 μ),
      ENNReal.toReal_nonneg (a := eLpNorm v 6 μ),
      Real.rpow_nonneg (ENNReal.toReal_nonneg (a := μ Set.univ)) (1 / 3 : ℝ)]
  have hpow : ((μ Set.univ).toReal ^ (1 / 3 : ℝ)) ^ 2 =
      (μ Set.univ).toReal ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast ENNReal.toReal_nonneg]
    norm_num
  simpa only [mul_pow, hpow, mul_comm] using hsq

/-- The actual Bochner-integral form used by the three-dimensional Yamabe
energy: the squared L2 norm is controlled by the squared L6 norm. -/
theorem integral_sq_le_volume_mul_integral_six [IsFiniteMeasure μ] (hv : MemLp v 6 μ) :
    (∫ x, |v x| ^ 2 ∂μ) ≤
      (μ Set.univ).toReal ^ (2 / 3 : ℝ) * (∫ x, |v x| ^ 6 ∂μ) ^ (1 / 3 : ℝ) := by
  have h := toReal_eLpNorm_two_sq_le_six hv
  have htwo : (eLpNorm v 2 μ).toReal =
      (∫ x, |v x| ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    rw [toReal_eLpNorm hv.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        hv.aestronglyMeasurable]
    norm_num [Real.norm_eq_abs, Real.rpow_natCast]
  have hsix : (eLpNorm v 6 μ).toReal =
      (∫ x, |v x| ^ 6 ∂μ) ^ (1 / 6 : ℝ) := by
    rw [toReal_eLpNorm hv.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        hv.aestronglyMeasurable]
    norm_num [Real.norm_eq_abs, Real.rpow_natCast]
  rw [htwo, hsix,
    ← Real.rpow_mul_natCast (integral_nonneg (fun x => pow_nonneg (abs_nonneg (v x)) 2)),
    ← Real.rpow_mul_natCast (integral_nonneg (fun x => pow_nonneg (abs_nonneg (v x)) 6))] at h
  norm_num at h ⊢
  exact h

#print axioms eLpNorm_two_le_six
#print axioms memLp_two_of_six
#print axioms toReal_eLpNorm_two_le_six
#print axioms toReal_eLpNorm_two_sq_le_six
#print axioms integral_sq_le_volume_mul_integral_six

end Yamabe3.Analysis
