import Yamabe3.Analysis.UniformElliptic.UniformJetEstimate

/-! # Actual L2 derivative profiles from common pointwise jet bounds -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A pointwise jet bound on the actual integration set gives the genuine
L2 profile bound with its volume factor; no regularity is a hidden premise. -/
theorem derivativeProfile_le_of_jet_bound
    {V : Set E} (hV : MeasurableSet V) (k : ℕ) {u : E → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hb : ∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n u x‖ ≤ A) :
    derivativeProfile 2 V k u ≤ (k + 1 : ℝ≥0∞) * ENNReal.ofReal A *
      (volume V) ^ (1 / 2 : ℝ) := by
  unfold derivativeProfile
  calc
    _ ≤ ∑ _n ∈ Finset.range (k + 1), ENNReal.ofReal A * (volume V) ^ (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have h : eLpNorm (fun x => ‖iteratedFDeriv ℝ n u x‖) 2 (volume.restrict V) ≤
          eLpNorm (fun _ : E => A) 2 (volume.restrict V) := by
        apply eLpNorm_mono_ae
        filter_upwards [ae_restrict_mem hV] with x hx
        rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg hA]
        exact hb n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) x hx
      apply h.trans_eq
      rw [eLpNorm_const' A (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), Real.enorm_eq_ofReal_abs, abs_of_nonneg hA,
        Measure.restrict_apply_univ]
      norm_num
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem derivativeProfile_ne_top_of_jet_bound
    {V : Set E} (hV : MeasurableSet V) (hfinite : volume V ≠ ⊤)
    (k : ℕ) {u : E → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n u x‖ ≤ A) :
    derivativeProfile 2 V k u ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (derivativeProfile_le_of_jet_bound hV k hA hb)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfinite)

/-- The real-valued form retains the true finite-volume factor. -/
theorem derivativeProfile_toReal_le_of_jet_bound
    {V : Set E} (hV : MeasurableSet V) (hfinite : volume V ≠ ⊤)
    (k : ℕ) {u : E → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ n ≤ k, ∀ x ∈ V, ‖iteratedFDeriv ℝ n u x‖ ≤ A) :
    (derivativeProfile 2 V k u).toReal ≤
      (k + 1 : ℝ) * A * (volume V).toReal ^ (1 / 2 : ℝ) := by
  have htop : (k + 1 : ℝ≥0∞) * ENNReal.ofReal A * (volume V) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfinite)
  have h := ENNReal.toReal_mono htop (derivativeProfile_le_of_jet_bound hV k hA hb)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_ofReal hA, ← ENNReal.toReal_rpow] at h
  exact h

#print axioms derivativeProfile_le_of_jet_bound
#print axioms derivativeProfile_ne_top_of_jet_bound
#print axioms derivativeProfile_toReal_le_of_jet_bound

end Yamabe3.Analysis.UniformElliptic
