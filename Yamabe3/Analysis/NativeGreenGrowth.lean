import Yamabe3.Analysis.Green.NativeCutoffParametrix

/-!
# Actual lower bound for a continuously corrected cutoff Green singularity

This uses the explicit native chart zero extension `singular e chi`, not an
assumed asymptotic expansion or an end-bound field. Continuity of the actual
correction at the pole supplies the bounded regular part. The conclusion is
on a punctured coordinate ball and then on an actual open neighborhood in M.
The arbitrary totalized value at the pole is deliberately excluded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M]

/-- The actual chart cutoff minus any correction continuous at the center
has the quantitative inverse-radius lower bound on a genuine punctured
coordinate ball. -/
theorem singular_sub_continuous_lower_bound
    (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (hχ : tsupport χ ⊆ e.source) {U : M → ℝ} (hU : ContinuousAt U (e 0)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ χ.rIn ∧
      ∀ x : E, 0 < ‖x‖ → ‖x‖ < r →
        (2 * ‖x‖)⁻¹ ≤ singular e χ (e x) - U (e x) := by
  have h0χ : (0 : E) ∈ tsupport χ := by
    rw [χ.tsupport_eq]
    exact mem_closedBall_self χ.rOut_pos.le
  have he : ContinuousAt e (0 : E) :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds (hχ h0χ))
  have hcomp : ContinuousAt (fun x : E => U (e x)) 0 := hU.comp he
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hcomp 1 (by norm_num)
  let C : ℝ := ‖U (e 0)‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let r : ℝ := min χ.rIn (min δ (2 * C)⁻¹)
  have hr : 0 < r := lt_min χ.rIn_pos (lt_min hδ (inv_pos.mpr (by positivity)))
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  intro x hx hxsmall
  have hxδ : ‖x‖ < δ := hxsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdiff : ‖U (e x) - U (e 0)‖ < 1 := by
    simpa only [dist_zero_right, dist_eq_norm] using hδbound (by simpa using hxδ)
  have hbound : ‖U (e x)‖ < C := by
    calc
      _ = ‖(U (e x) - U (e 0)) + U (e 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖U (e x) - U (e 0)‖ + ‖U (e 0)‖ := norm_add_le _ _
      _ < 1 + ‖U (e 0)‖ := by linarith
      _ = C := by dsimp [C]; ring
  have hxinv : ‖x‖ < (2 * C)⁻¹ :=
    hxsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hprod : ‖x‖ * (2 * C) < 1 := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp
    simpa only [one_div] using hxinv
  have hCinv : C < (2 * ‖x‖)⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * ‖x‖)).mpr
    nlinarith
  have hxinner : x ∈ closedBall 0 χ.rIn := by
    rw [mem_closedBall, dist_zero_right]
    exact (hxsmall.trans_le (min_le_left _ _)).le
  rw [singular_eq_inv_norm_near_center e χ hχ hxinner]
  have hsplit : ‖x‖⁻¹ = 2 * (2 * ‖x‖)⁻¹ := by
    field_simp
  rw [hsplit]
  have hpoint : U (e x) < (2 * ‖x‖)⁻¹ :=
    (le_abs_self _).trans_lt (hbound.trans hCinv)
  linarith

/-- The quantitative coordinate estimate gives positivity on an actual
open punctured neighborhood of the pole in the original manifold. -/
theorem singular_sub_continuous_pos_on_punctured_neighborhood
    (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (hχ : tsupport χ ⊆ e.source) {U : M → ℝ} (hU : ContinuousAt U (e 0)) :
    ∃ O : Set M, IsOpen O ∧ e 0 ∈ O ∧
      ∀ y ∈ O, y ≠ e 0 → 0 < singular e χ y - U y := by
  obtain ⟨r, hr, hrIn, hbound⟩ := singular_sub_continuous_lower_bound e χ hχ hU
  have hball : ball (0 : E) r ⊆ e.source := by
    intro x hx
    apply hχ
    rw [χ.tsupport_eq, mem_closedBall, dist_zero_right]
    exact ((by simpa using hx : ‖x‖ < r).trans_le hrIn).le.trans χ.rIn_lt_rOut.le
  refine ⟨e '' ball (0 : E) r, e.isOpen_image_of_subset_source isOpen_ball hball,
    mem_image_of_mem e (mem_ball_self hr), ?_⟩
  rintro y ⟨x, hx, rfl⟩ hxp
  have hx0 : x ≠ 0 := by intro hz; exact hxp (congrArg e hz)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  exact (inv_pos.mpr (mul_pos (by norm_num) hn)).trans_le
    (hbound x hn (by simpa using hx))

#print axioms singular_sub_continuous_lower_bound
#print axioms singular_sub_continuous_pos_on_punctured_neighborhood

end Yamabe3.Parametrix
