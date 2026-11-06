import GreenMass.PuncturedEnd
import Yamabe3.Analysis.Green.NativeCutoffParametrix

/-!
# The actual cutoff Newton singularity is a proper barrier on the puncture

The function is the already constructed native chart zero extension, restricted
to the inherited open manifold obtained by deleting its pole. Compactness of
all real sublevels is proved by excluding a genuine coordinate neighborhood of
the deleted point. No properness field or compactification is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GreenMass.SingularProperBarrier

open PuncturedEnd Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- The actual native singular cutoff on the actual inherited puncture. -/
def singularBarrier
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) : puncture (e 0) → ℝ :=
  fun q => singular e.toOpenPartialHomeomorph χ q.val

theorem contMDiff_singularBarrier
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (singularBarrier e χ) := by
  intro q
  apply (contMDiffAt_singular e.toOpenPartialHomeomorph e.contMDiffOn_invFun χ hχ
    (show q.val ≠ e 0 from q.property)).comp q
  exact contMDiff_subtype_val (I := 𝓡 3) (U := puncture (e 0)) (n := ∞) q

/-- Every finite sublevel excludes a genuine chart neighborhood of the pole,
and is a closed subset of the already proved compact complement of that end. -/
theorem isCompact_singularBarrier_sublevel [CompactSpace M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) (R : ℝ) :
    IsCompact {q : puncture (e 0) | singularBarrier e χ q ≤ R} := by
  let δ : ℝ := min χ.rIn (|R| + 1)⁻¹
  have hδ : 0 < δ := lt_min χ.rIn_pos (inv_pos.mpr (by positivity))
  have hδin : δ ≤ χ.rIn := min_le_left _ _
  have hδR : δ ≤ (|R| + 1)⁻¹ := min_le_right _ _
  have hball : ball (0 : E) δ ⊆ e.source := by
    intro x hx
    apply hχ
    rw [χ.tsupport_eq, mem_closedBall, dist_zero_right]
    exact ((by simpa using hx : ‖x‖ < δ).trans_le hδin).le.trans χ.rIn_lt_rOut.le
  apply (puncturedChartEnd_complement_isCompact e δ hδ hball).of_isClosed_subset
    (isClosed_le (contMDiff_singularBarrier e χ hχ).continuous continuous_const)
  intro q hq hqt
  rw [puncturedChartEnd_target e δ hδ hball] at hqt
  obtain ⟨x, hx, hxq⟩ := hqt
  have hx0 : x ≠ 0 := by
    intro hz
    exact q.property (by simp [← hxq, hz])
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxδ : ‖x‖ < δ := by simpa using hx
  have hxinner : x ∈ closedBall (0 : E) χ.rIn := by
    rw [mem_closedBall, dist_zero_right]
    exact (hxδ.trans_le hδin).le
  have hS : singularBarrier e χ q = ‖x‖⁻¹ := by
    unfold singularBarrier
    rw [← hxq]
    exact singular_eq_inv_norm_near_center e.toOpenPartialHomeomorph χ hχ hxinner
  have hmul : ‖x‖ * (|R| + 1) < 1 := by
    apply (lt_div_iff₀ (by positivity : 0 < |R| + 1)).mp
    simpa only [one_div] using hxδ.trans_le hδR
  have hlarge : |R| + 1 < ‖x‖⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hxn).mpr
    nlinarith
  have hRsmall : R < ‖x‖⁻¹ := by linarith [le_abs_self R]
  exact (not_le_of_gt hRsmall) (hS ▸ hq)

#print axioms contMDiff_singularBarrier
#print axioms isCompact_singularBarrier_sublevel

end GreenMass.SingularProperBarrier
