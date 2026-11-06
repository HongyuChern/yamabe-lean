import Yamabe3.Analysis.Green.NativeCutoffParametrix

/-!
# Actual normalized Green functions with pointwise C2 regular-part estimates

The derivatives below are the true Frechet derivatives of G composed with
the same constructed normal chart minus the Euclidean inverse radius. The
cutoff is identically one on a neighborhood of every evaluation point, so
all first and second jets equal those of the negative correction. No sphere
average or substitute regular-part definition is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Metric MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M]

/-- Actual cutoff germs identify both derivatives of the true regular part. -/
theorem regularPart_C2_of_correction
    (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (hχs : tsupport χ ⊆ e.source) (U : M → ℝ)
    {δ : ℝ} (hδχ : δ ≤ χ.rIn) (b C : ℝ)
    (hb : ∀ x : E, 0 < ‖x‖ → ‖x‖ < δ →
      ‖U (e x) - b‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
      ‖x‖ * ‖fderiv ℝ (fun y => U (e y)) x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
      ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ (fun y => U (e y))) x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ)) :
    ∀ x : E, 0 < ‖x‖ → ‖x‖ < δ →
      ‖(singular e χ (e x) - U (e x)) - ‖x‖⁻¹ - -b‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) ∧
      ‖x‖ * ‖fderiv ℝ (fun y => (singular e χ (e y) - U (e y)) - ‖y‖⁻¹) x‖ ≤
        C * ‖x‖ ^ (1 / 2 : ℝ) ∧
      ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ
        (fun y => (singular e χ (e y) - U (e y)) - ‖y‖⁻¹)) x‖ ≤
        C * ‖x‖ ^ (1 / 2 : ℝ) := by
  intro x hx hxδ
  have hxχ : x ∈ ball (0 : E) χ.rIn := by
    simpa using hxδ.trans_le hδχ
  have hg : (fun y : E => (singular e χ (e y) - U (e y)) - ‖y‖⁻¹) =ᶠ[𝓝 x]
      (fun y => -U (e y)) := by
    filter_upwards [isOpen_ball.mem_nhds hxχ] with y hy
    rw [singular_eq_inv_norm_near_center e χ hχs (ball_subset_closedBall hy)]
    ring
  have h := hb x hx hxδ
  refine ⟨?_, ?_, ?_⟩
  · have hg0 : singular e χ (e x) - U (e x) - ‖x‖⁻¹ = -U (e x) := hg.self_of_nhds
    rw [hg0]
    have heq : -U (e x) - -b = -(U (e x) - b) := by ring
    rw [heq, norm_neg]
    exact h.1
  · rw [hg.fderiv_eq, fderiv_fun_neg, norm_neg]
    exact h.2.1
  · have hneg : fderiv ℝ (fun y : E => -U (e y)) =
        (fun y => -fderiv ℝ (fun z => U (e z)) y) :=
      funext fun _ => fderiv_fun_neg
    rw [hg.fderiv.fderiv_eq, hneg, fderiv_fun_neg]
    change ‖x‖ ^ 2 * ‖-(fderiv ℝ (fderiv ℝ (fun z : E => U (e z))) x)‖ ≤ _
    have hn2 : ‖-(fderiv ℝ (fderiv ℝ (fun z : E => U (e z))) x)‖ =
        ‖fderiv ℝ (fderiv ℝ (fun z : E => U (e z))) x‖ := by
      convert! norm_neg (fderiv ℝ (fderiv ℝ (fun z : E => U (e z))) x)
    rw [hn2]
    exact h.2.2

#print axioms regularPart_C2_of_correction

end Yamabe3.Analysis.GreenParametrix
