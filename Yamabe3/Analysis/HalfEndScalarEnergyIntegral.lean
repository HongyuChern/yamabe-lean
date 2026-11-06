import Yamabe3.Analysis.HalfEndScalarCoercivity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The actual infinite-interval energy identity. Integrability is proved
from the nonnegative derivative of the actual endpoint energy and its
limit, rather than assumed as a weak/energy premise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology
namespace Yamabe3.Analysis.Delaunay

theorem halfEnd_scalar_total_energy_integral
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (hq : ∀ t : ℝ, 0 ≤ t → 0 ≤ q t)
    (hzdecay : Tendsto z atTop (𝓝 0)) (hdzdecay : Tendsto dz atTop (𝓝 0)) :
    IntegrableOn (fun t => dz t ^ 2 + q t * z t ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, dz t ^ 2 + q t * z t ^ 2) = -(dz 0) * z 0 := by
  have hc : ContinuousWithinAt (fun t => z t * dz t) (Ici 0) 0 :=
    (hz 0 le_rfl).continuousWithinAt.mul (hdz 0 (mem_Ici.mpr le_rfl))
  have hd (t : ℝ) (ht : t ∈ Ioi 0) :
      HasDerivAt (fun s => z s * dz s) (dz t ^ 2 + q t * z t ^ 2) t := by
    have h := ((hz t ht.le).hasDerivAt (Ici_mem_nhds ht)).mul (hode t ht)
    apply h.congr_deriv
    ring
  have hpos (t : ℝ) (ht : t ∈ Ioi 0) : 0 ≤ dz t ^ 2 + q t * z t ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg (hq t ht.le) (sq_nonneg _))
  have hlim : Tendsto (fun t => z t * dz t) atTop (𝓝 0) := by
    simpa only [mul_zero] using hzdecay.mul hdzdecay
  have hint := integrableOn_Ioi_deriv_of_nonneg hc hd hpos hlim
  refine ⟨hint, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint hlim
  exact h.trans (by ring)

theorem halfEnd_scalar_derivative_square_integral
    (z dz q : ℝ → ℝ)
    (hz : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt z (dz t) (Ici 0) t)
    (hdz : ContinuousOn dz (Ici 0))
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt dz (q t * z t) t)
    (hq : ∀ t : ℝ, 0 ≤ t → 0 ≤ q t)
    (hzdecay : Tendsto z atTop (𝓝 0)) (hdzdecay : Tendsto dz atTop (𝓝 0)) :
    IntegrableOn (fun t => dz t ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, dz t ^ 2) ≤ -(dz 0) * z 0 := by
  obtain ⟨he, heq⟩ := halfEnd_scalar_total_energy_integral z dz q hz hdz hode hq hzdecay hdzdecay
  have hi : IntegrableOn (fun t => dz t ^ 2) (Ioi 0) := by
    apply he.mono' (((hdz.mono Ioi_subset_Ici_self).pow 2).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_right (mul_nonneg (hq t ht.le) (sq_nonneg _))
  refine ⟨hi, ?_⟩
  rw [← heq]
  apply integral_mono_ae hi he
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_add_of_nonneg_right (mul_nonneg (hq t ht.le) (sq_nonneg _))

#print axioms halfEnd_scalar_total_energy_integral
#print axioms halfEnd_scalar_derivative_square_integral
end Yamabe3.Analysis.Delaunay
