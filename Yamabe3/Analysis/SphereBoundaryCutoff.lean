import Yamabe3.Analysis.SphereBoundaryLayer
import Yamabe3.Analysis.EuclideanSphereTrace
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth physical exterior cutoffs and convergence of actual volume terms

The cutoff is identically zero on the closed inner ball and identically
one beyond the true transition layer. Smoothness at the origin follows
from its actual local constancy. Its bounded pointwise convergence gives
dominated convergence for every integrable native-volume payload, with no
boundary-null-set assumption or implicit source-norm change.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer

def exteriorSphereCutoff (r ε : ℝ) (x : E) : ℝ := exteriorLayerProfile r ε ‖x‖

theorem exteriorSphereCutoff_nonneg (r ε : ℝ) (x : E) :
    0 ≤ exteriorSphereCutoff r ε x := Real.smoothTransition.nonneg _

theorem exteriorSphereCutoff_le_one (r ε : ℝ) (x : E) :
    exteriorSphereCutoff r ε x ≤ 1 := Real.smoothTransition.le_one _

theorem exteriorLayerProfile_eq_zero {r ε s : ℝ} (hε : 0 < ε) (hs : s ≤ r) :
    exteriorLayerProfile r ε s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hε.le)

theorem exteriorLayerProfile_eq_one {r ε s : ℝ} (hε : 0 < ε) (hs : r + ε ≤ s) :
    exteriorLayerProfile r ε s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hε).mpr
  linarith only [hs]

theorem exteriorLayerProfile_deriv_eq_zero_of_outside {r ε s : ℝ}
    (hε : 0 < ε) (hs : s ∉ Ioo r (r + ε)) :
    deriv (exteriorLayerProfile r ε) s = 0 := by
  have hsplit : s ≤ r ∨ r + ε ≤ s := by
    by_cases h : s ≤ r
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt fun ht => hs ⟨lt_of_not_ge h, ht⟩)
  rcases hsplit with hleft | hright
  · have hm : IsLocalMin (exteriorLayerProfile r ε) s := by
      change ∀ᶠ t in 𝓝 s, exteriorLayerProfile r ε s ≤ exteriorLayerProfile r ε t
      rw [exteriorLayerProfile_eq_zero hε hleft]
      exact Eventually.of_forall fun t => Real.smoothTransition.nonneg _
    exact hm.deriv_eq_zero
  · have hm : IsLocalMax (exteriorLayerProfile r ε) s := by
      change ∀ᶠ t in 𝓝 s, exteriorLayerProfile r ε t ≤ exteriorLayerProfile r ε s
      rw [exteriorLayerProfile_eq_one hε hright]
      exact Eventually.of_forall fun t => Real.smoothTransition.le_one _
    exact hm.deriv_eq_zero

theorem exteriorSphereCutoff_smooth {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ ∞ (exteriorSphereCutoff r ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : E => (0 : ℝ)) contDiffAt_const
    filter_upwards [ball_mem_nhds (0 : E) hr] with y hy
    have hyn : ‖y‖ < r := by simpa only [mem_ball, dist_zero_right] using hy
    exact exteriorLayerProfile_eq_zero hε hyn.le
  · exact (exteriorLayerProfile_smooth r ε).contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem tendsto_exteriorSphereCutoff (r : ℝ) (x : E) :
    Tendsto (fun ε : ℝ => exteriorSphereCutoff r ε x) (𝓝[>] 0)
      (𝓝 (({y : E | r < ‖y‖}).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : r < ‖x‖
  · rw [indicator_of_mem (show x ∈ {y : E | r < ‖y‖} from hx)]
    apply tendsto_const_nhds.congr'
    have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ‖x‖ - r :=
      (eventually_lt_nhds (sub_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hevent] with ε hε hεr
    exact (exteriorLayerProfile_eq_one hε (by linarith only [hεr])).symm
  · rw [indicator_of_notMem (show x ∉ {y : E | r < ‖y‖} from hx)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (exteriorLayerProfile_eq_zero hε (le_of_not_gt hx)).symm

/-- Every integrable volume payload converges on the actual exterior of
the closed ball, with the same measure and no claim about stronger norms. -/
theorem tendsto_integral_exteriorSphereCutoff {r : ℝ} (hr : 0 < r)
    {μ : Measure E} {H : E → ℝ} (hH : Integrable H μ) :
    Tendsto (fun ε : ℝ => ∫ x, exteriorSphereCutoff r ε x * H x ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x in {y : E | r < ‖y‖}, H x ∂μ)) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ x, exteriorSphereCutoff r ε x * H x ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x,
        (({y : E | r < ‖y‖}).indicator (fun _ => (1 : ℝ)) x) * H x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖H x‖)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((exteriorSphereCutoff_smooth hr hε).continuous.aestronglyMeasurable).mul hH.1
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exteriorSphereCutoff_nonneg r ε x)]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (exteriorSphereCutoff_le_one r ε x) (norm_nonneg (H x))
    · exact hH.norm
    · exact Eventually.of_forall fun x => (tendsto_exteriorSphereCutoff r x).mul_const (H x)
  have heq : (∫ x, (({y : E | r < ‖y‖}).indicator (fun _ => (1 : ℝ)) x) * H x ∂μ) =
      ∫ x in {y : E | r < ‖y‖}, H x ∂μ := by
    rw [← integral_indicator (isOpen_lt continuous_const continuous_norm).measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : r < ‖x‖ <;> simp [hx]
  rwa [heq] at hlim

#print axioms exteriorSphereCutoff_smooth
#print axioms tendsto_integral_exteriorSphereCutoff

end Yamabe3.Analysis.EuclideanSphereTrace
