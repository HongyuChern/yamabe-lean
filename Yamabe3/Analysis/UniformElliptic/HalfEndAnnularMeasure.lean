import Yamabe3.Analysis.UniformElliptic.HalfEndEntranceCollar
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Actual annular measure comparisons for normalized physical end slices

The finite-cover inequality is proved for the actual restricted Euclidean
measure. Contraction by one half has pushforward factor eight in dimension
three. Its L2 factor is deliberately bounded above by eight; it is never
discarded. Local smoothness suffices for the derivative-profile comparison.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Subadditivity of the actual L2 norm under addition of measures. -/
theorem eLpNorm_two_add_measure_le (f : E3 → ℝ) (μ ν : Measure E3) :
    eLpNorm f 2 (μ + ν) ≤ eLpNorm f 2 μ + eLpNorm f 2 ν := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
  rw [lintegral_add_measure]
  exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)

/-- A finite annular cover controls the same profile by the sum of profiles
on its pieces, without removing boundary spheres. -/
theorem derivativeProfile_union_le (A B : Set E3) (u : E3 → ℝ) (k : ℕ) :
    derivativeProfile 2 (A ∪ B) k u ≤
      derivativeProfile 2 A k u + derivativeProfile 2 B k u := by
  unfold derivativeProfile
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact (eLpNorm_mono_measure (fun x : E3 => ‖iteratedFDeriv ℝ j u x‖)
    (Measure.restrict_union_le A B)).trans
      (eLpNorm_two_add_measure_le (fun x : E3 => ‖iteratedFDeriv ℝ j u x‖)
        (volume.restrict A) (volume.restrict B))

/-- The literal Haar determinant of contraction by one half in dimension
three. This is the measure used in every following profile estimate. -/
theorem map_volume_half_dilation :
    Measure.map (fun x : E3 => (1 / 2 : ℝ) • x) volume =
      (8 : ℝ≥0∞) • (volume : Measure E3) := by
  rw [Measure.map_addHaar_smul volume (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  norm_num [finrank_euclideanSpace]

/-- The actual L2 pullback estimate for contraction by one half. The
nonsharp factor eight bounds the correct square-root determinant factor. -/
theorem eLpNorm_half_dilation_le {Ω Γ : Set E3}
    (himage : ∀ x ∈ Ω, (1 / 2 : ℝ) • x ∈ Γ) (f : E3 → ℝ) :
    eLpNorm (fun x : E3 => f ((1 / 2 : ℝ) • x)) 2 (volume.restrict Ω) ≤
      8 * eLpNorm f 2 (volume.restrict Γ) := by
  have he : MeasurableEmbedding (fun x : E3 => (1 / 2 : ℝ) • x) :=
    (Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num)).measurableEmbedding
  have hm : Measure.map (fun x : E3 => (1 / 2 : ℝ) • x) (volume.restrict Ω) ≤
      (8 : ℝ≥0∞) • (volume : Measure E3).restrict Γ := by
    calc
      _ ≤ Measure.map (fun x : E3 => (1 / 2 : ℝ) • x)
          (volume.restrict ((fun x : E3 => (1 / 2 : ℝ) • x) ⁻¹' Γ)) :=
        Measure.map_mono (Measure.restrict_mono_set volume himage) he.measurable
      _ = (Measure.map (fun x : E3 => (1 / 2 : ℝ) • x) volume).restrict Γ :=
        (he.restrict_map volume Γ).symm
      _ = _ := by rw [map_volume_half_dilation, Measure.restrict_smul]
  have hfactor : (8 : ℝ≥0∞) ^ ((1 / (2 : ℝ≥0∞)).toReal) ≤ 8 := by
    have hh := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 8)
      (by norm_num : ((1 / (2 : ℝ≥0∞)).toReal) ≤ (1 : ℝ))
    simpa only [ENNReal.rpow_one] using hh
  change eLpNorm (f ∘ (fun x : E3 => (1 / 2 : ℝ) • x)) 2 (volume.restrict Ω) ≤ _
  rw [← he.eLpNorm_map_measure]
  exact (eLpNorm_le_of_measure_le_smul hm).trans
    (mul_le_mul_of_nonneg_right hfactor zero_le)

/-- All jets contract under one-half dilation and a scalar of modulus at
most one. The actual volume change is the remaining factor eight. -/
theorem derivativeProfile_scalar_half_dilation_le
    {O Ω Γ : Set E3} (hO : IsOpen O) (hΩ : MeasurableSet Ω)
    (hΓO : Γ ⊆ O) {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (k : ℕ) {c : ℝ} (hc : |c| ≤ 1)
    (himage : ∀ x ∈ Ω, (1 / 2 : ℝ) • x ∈ Γ) :
    derivativeProfile 2 Ω k (fun x : E3 => c * u ((1 / 2 : ℝ) • x)) ≤
      8 * derivativeProfile 2 Γ k u := by
  unfold derivativeProfile
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ eLpNorm (fun x : E3 => ‖iteratedFDeriv ℝ j u ((1 / 2 : ℝ) • x)‖) 2
        (volume.restrict Ω) := by
      apply eLpNorm_mono_ae_real
      filter_upwards [ae_restrict_mem hΩ] with x hx
      rw [norm_norm, norm_iteratedFDeriv_scalar_local_dilation hO hu j c
        (by norm_num : (0 : ℝ) ≤ 1 / 2) x (hΓO (himage x hx))]
      have hcoeff : |c| * (1 / 2 : ℝ) ^ j ≤ 1 :=
        mul_le_one₀ hc (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := eLpNorm_half_dilation_le himage (fun x : E3 => ‖iteratedFDeriv ℝ j u x‖)

#print axioms eLpNorm_two_add_measure_le
#print axioms derivativeProfile_union_le
#print axioms map_volume_half_dilation
#print axioms eLpNorm_half_dilation_le
#print axioms derivativeProfile_scalar_half_dilation_le

end Yamabe3.Analysis.UniformElliptic
