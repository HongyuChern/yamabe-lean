import Yamabe3.Analysis.UniformElliptic.NativeAnnularJet

/-!
# Same-function pointwise C2 remainder estimates

This is the concrete order-zero/one/two interface for the actual native
correction. Both first and second derivatives are genuine Frechet operator
norms. One positive radius and one constant serve all three estimates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Yamabe3.Analysis.GreenParametrix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_native_correction_C2_bound
    (g : RiemannianMetric 3 E3)
    (hB : g.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E3))
    {R : ℝ} (hR : 0 < R) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball (0 : E3) R \ {0}))
    (hP : ∀ y ∈ ball (0 : E3) R \ {0},
      -g.leviCivitaData.laplacian u y +
        (g.leviCivitaData.scalarCurvature y / 8) * u y = nativeResidual g χ y)
    (b H : ℝ) (hH : 0 ≤ H)
    (hholder : ∀ y ∈ ball (0 : E3) R \ {0}, ‖u y - b‖ ≤ H * ‖y‖ ^ (1 / 2 : ℝ)) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ R ∧ 0 ≤ C ∧ ∀ x : E3, 0 < ‖x‖ → ‖x‖ < δ →
      ‖u x - b‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
      ‖x‖ * ‖fderiv ℝ u x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
      ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨δ1, C1, hδ1, hC1, h1⟩ := exists_native_correction_weighted_jet_bound
    g hB hρ hzero χ hR hu hP b H hH hholder 1 (by norm_num)
  obtain ⟨δ2, C2, hδ2, hC2, h2⟩ := exists_native_correction_weighted_jet_bound
    g hB hρ hzero χ hR hu hP b H hH hholder 2 (by norm_num)
  let δ := min R (min δ1 δ2)
  let C := max H (max C1 C2)
  refine ⟨δ, C, lt_min hR (lt_min hδ1 hδ2), min_le_left _ _,
    hH.trans (le_max_left _ _), ?_⟩
  intro x hx hxδ
  have hxR : x ∈ ball (0 : E3) R \ {0} := by
    refine ⟨?_, norm_pos_iff.mp hx⟩
    simpa using hxδ.trans_le (min_le_left _ _)
  have hx1 : ‖x‖ < δ1 := hxδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hx2 : ‖x‖ < δ2 := hxδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpow : 0 ≤ ‖x‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨(hholder x hxR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow), ?_, ?_⟩
  · have h := h1 x hx hx1
    simp only [pow_one, norm_iteratedFDeriv_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C1 C2).trans (le_max_right H _)) hpow)
  · have h := h2 x hx hx2
    have heq : ‖iteratedFDeriv ℝ 2 u x‖ = ‖fderiv ℝ (fderiv ℝ u) x‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [heq] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((le_max_right C1 C2).trans (le_max_right H _)) hpow)

#print axioms exists_native_correction_C2_bound

end Yamabe3.Analysis.UniformElliptic
