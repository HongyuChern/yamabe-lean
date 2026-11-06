import Yamabe3.Analysis.Green.RescaledResidual

/-!
# A single C2 bound for the actual rescaled source family

The compactness argument is applied to the jointly smooth extension and its
actual partial derivatives before selecting the scale. Thus the resulting
constant controls every scale in the fixed compact interval at once.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace Yamabe3.Analysis.GreenParametrix

/-- A compact annulus and a compact scale interval give one genuine common
constant for the actual rescaled density residual and its first two spatial
Frechet derivatives, including scale zero. -/
theorem exists_uniform_scaledDensityResidual_C2_bound {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) (hV : ContDiff ℝ ∞ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0 : ℝ) 1, ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖scaledDensityResidual ρ V (r, z)‖ ≤ C ∧
      ‖fderiv ℝ (fun x => scaledDensityResidual ρ V (r, x)) z‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => scaledDensityResidual ρ V (r, x))) z‖ ≤ C := by
  let F : ℝ × E → ℝ := scaledDensityResidual ρ V
  let L : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  let D1 : ℝ × E → E →L[ℝ] ℝ := fun q => (fderiv ℝ F q).comp L
  let D2 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun q => (fderiv ℝ D1 q).comp L
  have hF (q : ℝ × E) (hq : q.2 ≠ 0) : ContDiffAt ℝ ∞ F q :=
    contDiffAt_scaledDensityResidual hρ hpos hV q hq
  have hD1 (q : ℝ × E) (hq : q.2 ≠ 0) : ContDiffAt ℝ ∞ D1 q :=
    ((hF q hq).fderiv_right (by simp)).clm_comp contDiffAt_const
  have hD2 (q : ℝ × E) (hq : q.2 ≠ 0) : ContDiffAt ℝ ∞ D2 q :=
    ((hD1 q hq).fderiv_right (by simp)).clm_comp contDiffAt_const
  let K : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ
    (closedBall (0 : E) 2 \ ball (0 : E) (1 / 2))
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall (0 : E) 2).diff isOpen_ball)
  have hKzero (q : ℝ × E) (hq : q ∈ K) : q.2 ≠ 0 := by
    intro hz
    have hn := hq.2.2
    apply hn
    simp [hz]
  have hFc : ContinuousOn F K := fun q hq => (hF q (hKzero q hq)).continuousAt.continuousWithinAt
  have hD1c : ContinuousOn D1 K := fun q hq => (hD1 q (hKzero q hq)).continuousAt.continuousWithinAt
  have hD2c : ContinuousOn D2 K := fun q hq => (hD2 q (hKzero q hq)).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hFc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hD1c
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (f := D2) (by convert! hD2c)
  let C : ℝ := max 0 (max A (max B D))
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : B ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hDC : D ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hfirst (r : ℝ) (z : E) (hz : z ≠ 0) :
      fderiv ℝ (fun x => F (r, x)) z = D1 (r, z) :=
    (((hF (r, z) hz).differentiableAt (by simp)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right r z)).fderiv
  refine ⟨C, le_max_left _ _, ?_⟩
  intro r hr z hzlo hzup
  have hz : z ≠ 0 := by intro heq; norm_num [heq] at hzlo
  have hmem : (r, z) ∈ K := by
    refine ⟨hr, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right] using hzup
    · simpa only [mem_ball, dist_zero_right, not_lt] using hzlo
  have hsecond : fderiv ℝ (fderiv ℝ (fun x => F (r, x))) z = D2 (r, z) := by
    have heq : fderiv ℝ (fun x => F (r, x)) =ᶠ[𝓝 z] fun x => D1 (r, x) := by
      filter_upwards [eventually_ne_nhds hz] with x hx
      exact hfirst r x hx
    rw [heq.fderiv_eq]
    exact (((hD1 (r, z) hz).differentiableAt (by simp)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right r z)).fderiv
  exact ⟨(hA _ hmem).trans hAC,
    by change ‖fderiv ℝ (fun x => F (r, x)) z‖ ≤ C; rw [hfirst r z hz]; exact (hB _ hmem).trans hBC,
    by
      change ‖fderiv ℝ (fderiv ℝ (fun x => F (r, x))) z‖ ≤ C
      rw [hsecond]
      exact (hD _ hmem).trans hDC⟩

#print axioms exists_uniform_scaledDensityResidual_C2_bound

end Yamabe3.Analysis.GreenParametrix
