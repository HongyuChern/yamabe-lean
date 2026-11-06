import Yamabe3.Analysis.SphereBoundaryCutoff
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateTest

/-!
# Actual exterior cutoffs on the original manifold

The cutoff is one minus the zero extension of the inner coordinate cutoff.
Its smoothness follows from its actual compact coordinate support. Its limit
is the indicator of the complement of the actual closed chart ball, including
the boundary convention. Dominated convergence retains the supplied native
measure and every genuinely integrable volume payload.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The literal cutoff equals one away from the chart, not zero. -/
def chartExteriorCutoff (e : OpenPartialHomeomorph E M) (r ε : ℝ) (y : M) : ℝ :=
  1 - coordinateExtension e (fun x => 1 - exteriorSphereCutoff r ε x) y

theorem innerSphereCutoff_tsupport_subset {r ε : ℝ} (hε : 0 < ε) :
    tsupport (fun x : E => 1 - exteriorSphereCutoff r ε x) ⊆ closedBall 0 (r + ε) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  change 1 - exteriorSphereCutoff r ε x ≠ 0 at hx
  by_contra hn
  have hnorm : r + ε < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  exact hx (by rw [show exteriorSphereCutoff r ε x = 1 from
    exteriorLayerProfile_eq_one hε hnorm.le, sub_self])

theorem innerSphereCutoff_compactSupport {r ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fun x : E => 1 - exteriorSphereCutoff r ε x) :=
  (isCompact_closedBall (0 : E) (r + ε)).of_isClosed_subset
    (isClosed_tsupport _) (innerSphereCutoff_tsupport_subset hε)

@[simp] theorem chartExteriorCutoff_comp_apply (e : OpenPartialHomeomorph E M)
    (r ε : ℝ) {x : E} (hx : x ∈ e.source) :
    chartExteriorCutoff e r ε (e x) = exteriorSphereCutoff r ε x := by
  rw [chartExteriorCutoff, coordinateExtension_comp_apply e _ hx]
  ring

theorem chartExteriorCutoff_eq_one_outside (e : OpenPartialHomeomorph E M)
    (r ε : ℝ) {y : M} (hy : y ∉ e.target) : chartExteriorCutoff e r ε y = 1 := by
  rw [chartExteriorCutoff, coordinateExtension, indicator_of_notMem hy, sub_zero]

theorem chartExteriorCutoff_range (e : OpenPartialHomeomorph E M) (r ε : ℝ) (y : M) :
    0 ≤ chartExteriorCutoff e r ε y ∧ chartExteriorCutoff e r ε y ≤ 1 := by
  by_cases hy : y ∈ e.target
  · rw [chartExteriorCutoff, coordinateExtension_apply e _ hy]
    constructor <;> linarith [exteriorSphereCutoff_nonneg r ε (e.symm y),
      exteriorSphereCutoff_le_one r ε (e.symm y)]
  · rw [chartExteriorCutoff_eq_one_outside e r ε hy]
    exact ⟨zero_le_one, le_rfl⟩

theorem chartExteriorCutoff_smooth (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hs : closedBall (0 : E) (r + ε) ⊆ e.source) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (chartExteriorCutoff e r ε) :=
  contMDiff_const.sub (contMDiff_coordinateExtension e hei
    (contDiff_const.sub (exteriorSphereCutoff_smooth hr hε))
    (innerSphereCutoff_compactSupport hε) ((innerSphereCutoff_tsupport_subset hε).trans hs))

theorem mem_chart_closedBall_iff (e : OpenPartialHomeomorph E M)
    {r : ℝ} (hs : closedBall (0 : E) r ⊆ e.source) {y : M} (hy : y ∈ e.target) :
    y ∈ e '' closedBall (0 : E) r ↔ ‖e.symm y‖ ≤ r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [e.left_inv (hs hx)]
    simpa only [mem_closedBall, dist_zero_right] using hx
  · intro hx
    exact ⟨e.symm y, by simpa only [mem_closedBall, dist_zero_right] using hx, e.right_inv hy⟩

theorem tendsto_chartExteriorCutoff (e : OpenPartialHomeomorph E M)
    {r : ℝ} (hs : closedBall (0 : E) r ⊆ e.source) (y : M) :
    Tendsto (fun ε : ℝ => chartExteriorCutoff e r ε y) (𝓝[>] 0)
      (𝓝 ((e '' closedBall (0 : E) r)ᶜ.indicator (fun _ => (1 : ℝ)) y)) := by
  by_cases hy : y ∈ e.target
  · have hfun (ε : ℝ) : chartExteriorCutoff e r ε y = exteriorSphereCutoff r ε (e.symm y) := by
      rw [chartExteriorCutoff, coordinateExtension_apply e _ hy]
      ring
    have heq : (({z : E | r < ‖z‖}).indicator (fun _ => (1 : ℝ)) (e.symm y)) =
        (e '' closedBall (0 : E) r)ᶜ.indicator (fun _ => (1 : ℝ)) y := by
      by_cases hn : r < ‖e.symm y‖
      · have hyc : y ∈ (e '' closedBall (0 : E) r)ᶜ := by
          change y ∉ e '' closedBall (0 : E) r
          rw [mem_chart_closedBall_iff e hs hy]
          exact not_le.mpr hn
        simp only [indicator_of_mem (show e.symm y ∈ {z : E | r < ‖z‖} from hn), indicator_of_mem hyc]
      · have hyc : y ∉ (e '' closedBall (0 : E) r)ᶜ := by
          simp only [mem_compl_iff, not_not]
          exact (mem_chart_closedBall_iff e hs hy).mpr (le_of_not_gt hn)
        simp only [indicator_of_notMem (show e.symm y ∉ {z : E | r < ‖z‖} from hn), indicator_of_notMem hyc]
    simpa only [hfun, heq] using tendsto_exteriorSphereCutoff r (e.symm y)
  · have hyc : y ∈ (e '' closedBall (0 : E) r)ᶜ := by
      rintro ⟨x, hx, rfl⟩
      exact hy (e.map_source (hs hx))
    simpa only [chartExteriorCutoff_eq_one_outside e r _ hy, indicator_of_mem hyc]
      using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1))

variable [MeasurableSpace M] [BorelSpace M]

theorem tendsto_integral_chartExteriorCutoff (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hs : closedBall (0 : E) R ⊆ e.source) {μ : Measure M} {H : M → ℝ}
    (hH : Integrable H μ) :
    Tendsto (fun ε : ℝ => ∫ y, chartExteriorCutoff e r ε y * H y ∂μ)
      (𝓝[>] 0) (𝓝 (∫ y in (e '' closedBall (0 : E) r)ᶜ, H y ∂μ)) := by
  have hrs : closedBall (0 : E) r ⊆ e.source :=
    (closedBall_subset_closedBall hrR.le).trans hs
  have hset : MeasurableSet ((e '' closedBall (0 : E) r)ᶜ) :=
    ((isCompact_closedBall (0 : E) r).image_of_continuousOn
      (e.continuousOn.mono hrs)).isClosed.isOpen_compl.measurableSet
  have hlim : Tendsto (fun ε : ℝ => ∫ y, chartExteriorCutoff e r ε y * H y ∂μ)
      (𝓝[>] 0) (𝓝 (∫ y, ((e '' closedBall (0 : E) r)ᶜ.indicator
        (fun _ => (1 : ℝ)) y) * H y ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖H y‖)
    · have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < R - r :=
        (eventually_lt_nhds (sub_pos.mpr hrR)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hevent] with ε hε hεR
      have hsε : closedBall (0 : E) (r + ε) ⊆ e.source :=
        (closedBall_subset_closedBall (by linarith only [hεR])).trans hs
      exact (chartExteriorCutoff_smooth e hei hr hε hsε).continuous.aestronglyMeasurable.mul hH.1
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (chartExteriorCutoff_range e r ε y).1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (chartExteriorCutoff_range e r ε y).2 (norm_nonneg (H y))
    · exact hH.norm
    · exact Eventually.of_forall fun y => (tendsto_chartExteriorCutoff e hrs y).mul_const (H y)
  have heq : (∫ y, ((e '' closedBall (0 : E) r)ᶜ.indicator
      (fun _ => (1 : ℝ)) y) * H y ∂μ) = ∫ y in (e '' closedBall (0 : E) r)ᶜ, H y ∂μ := by
    rw [← integral_indicator hset]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ (e '' closedBall (0 : E) r)ᶜ <;> simp [hy]
  rwa [heq] at hlim

#print axioms chartExteriorCutoff_smooth
#print axioms tendsto_integral_chartExteriorCutoff

end Yamabe3.Analysis.EuclideanSphereTrace
