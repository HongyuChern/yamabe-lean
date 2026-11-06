import Yamabe3.Analysis.SpectralDiagonalKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convolution

/-!
# Exact integrability of the Hilbert-valued diagonal kernel

Splitting the two half-lines preserves the sharp conjugated denominator
k0^2-delta^2. The proof does not replace delta by its absolute value in
both rates, which would lose the weights required in the gluing range.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology lp
namespace Yamabe3.Analysis.Delaunay

def spectralMajorant (k₀ δ t : ℝ) : ℝ := Real.exp (-δ * t - k₀ * |t|) / (2 * k₀)

theorem spectralMajorant_nonneg {k₀ : ℝ} (hk₀ : 0 < k₀) (δ t : ℝ) :
    0 ≤ spectralMajorant k₀ δ t := by unfold spectralMajorant; positivity

theorem spectralMajorant_left (k₀ δ : ℝ) {t : ℝ} (ht : t ≤ 0) :
    spectralMajorant k₀ δ t = Real.exp ((k₀ - δ) * t) / (2 * k₀) := by
  unfold spectralMajorant
  rw [abs_of_nonpos ht]
  congr 2; ring

theorem spectralMajorant_right (k₀ δ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    spectralMajorant k₀ δ t = Real.exp (-(k₀ + δ) * t) / (2 * k₀) := by
  unfold spectralMajorant
  rw [abs_of_nonneg ht]
  congr 2; ring

/-- Actual integrability and the exact integral of the operator norm majorant. -/
theorem spectralMajorant_integral {k₀ δ : ℝ} (hk₀ : 0 < k₀) (hδ : |δ| < k₀) :
    Integrable (spectralMajorant k₀ δ) ∧
      (∫ t : ℝ, spectralMajorant k₀ δ t) = 1 / (k₀ ^ 2 - δ ^ 2) := by
  have hm : 0 < k₀ - δ := by linarith [(abs_lt.mp hδ).2]
  have hp : 0 < k₀ + δ := by linarith [(abs_lt.mp hδ).1]
  have heL : (fun t : ℝ => Real.exp ((k₀ - δ) * t) / (2 * k₀)) =ᵐ[volume.restrict (Iic 0)]
      spectralMajorant k₀ δ := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact (spectralMajorant_left k₀ δ ht).symm
  have heR : (fun t : ℝ => Real.exp (-(k₀ + δ) * t) / (2 * k₀)) =ᵐ[volume.restrict (Ioi 0)]
      spectralMajorant k₀ δ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (spectralMajorant_right k₀ δ ht.le).symm
  have hL : IntegrableOn (spectralMajorant k₀ δ) (Iic 0) :=
    ((integrableOn_exp_mul_Iic hm 0).div_const (2 * k₀)).congr heL
  have hR : IntegrableOn (spectralMajorant k₀ δ) (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) 0).div_const (2 * k₀)).congr heR
  have hint : Integrable (spectralMajorant k₀ δ) := by
    have h := integrableOn_union.mpr ⟨hL, hR⟩
    simpa only [Iic_union_Ioi, integrableOn_univ] using h
  refine ⟨hint, ?_⟩
  rw [← integral_add_compl measurableSet_Iic hint, compl_Iic,
    ← integral_congr_ae heL, ← integral_congr_ae heR,
    integral_div, integral_div, integral_exp_mul_Iic hm 0,
    integral_exp_mul_Ioi (neg_neg_of_pos hp) 0]
  simp only [mul_zero, Real.exp_zero]
  have hden : k₀ ^ 2 - δ ^ 2 ≠ 0 := by
    have hprod : 0 < (k₀ - δ) * (k₀ + δ) := mul_pos hm hp
    nlinarith
  field_simp
  ring

theorem weightedSpectralKernel_integrable {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀) :
    Integrable (weightedSpectralKernel k hk₀ hk δ) := by
  apply (spectralMajorant_integral hk₀ hδ).1.mono'
    (weightedSpectralKernel_continuous k hk₀ hk δ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (weightedSpectralKernel_norm_le k hk₀ hk δ)

end Yamabe3.Analysis.Delaunay
