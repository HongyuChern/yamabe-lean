import Yamabe3.Analysis.NativeChartExteriorCutoff

/-!
# Cutoffs with genuine support inside the actual exterior domain

The inner edge is a+δ and the outer edge is a+2δ. Thus the
topological support is contained in the complement of the closed ball
of radius a, as required by the actual H1-zero completion. The value
agrees with the exterior indicator outside the same shrinking collar.
These statements concern the original chart image and literal cutoff.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold

namespace Yamabe3.Analysis.EuclideanSphereTrace

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet SphereBoundaryLayer

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem chartExteriorCutoff_eq_one_of_notMem_chart_ball
    (e : OpenPartialHomeomorph E M) {r δ : ℝ} (hδ : 0 < δ)
    (hs : closedBall (0 : E) (r + δ) ⊆ e.source)
    {y : M} (hy : y ∉ e '' closedBall (0 : E) (r + δ)) :
    chartExteriorCutoff e r δ y = 1 := by
  have hsub : tsupport (coordinateExtension e (fun x => 1 - exteriorSphereCutoff r δ x)) ⊆
      e '' closedBall (0 : E) (r + δ) :=
    (tsupport_coordinateExtension_subset_image e (innerSphereCutoff_compactSupport hδ)
      ((innerSphereCutoff_tsupport_subset hδ).trans hs)).trans
        (image_mono (innerSphereCutoff_tsupport_subset hδ))
  have hz := image_eq_zero_of_notMem_tsupport (f := coordinateExtension e
    (fun x => 1 - exteriorSphereCutoff r δ x)) (fun ht => hy (hsub ht))
  rw [chartExteriorCutoff, hz, sub_zero]

/-- The shift provides a real open zero neighborhood of the deleted
closed ball; pointwise vanishing on its boundary alone would not suffice. -/
theorem shifted_chartExteriorCutoff_tsupport_subset
    (e : OpenPartialHomeomorph E M) {a δ : ℝ} (hδ : 0 < δ)
    (hs : closedBall (0 : E) (a + 2 * δ) ⊆ e.source) :
    tsupport (chartExteriorCutoff e (a + δ) δ) ⊆
      (e '' closedBall (0 : E) a)ᶜ := by
  intro y hy
  change y ∉ e '' closedBall (0 : E) a
  rintro ⟨x, hx, rfl⟩
  have hnorm : ‖x‖ ≤ a := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hxs : x ∈ e.source := hs (by
    simp only [mem_closedBall, dist_zero_right]
    linarith)
  have hyt := e.map_source hxs
  have hc : ContinuousAt (fun z : M => ‖e.symm z‖) (e x) :=
    (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hyt)).norm
  have hlt : ‖e.symm (e x)‖ < a + δ := by rw [e.left_inv hxs]; linarith
  have hn : ∀ᶠ z in 𝓝 (e x), ‖e.symm z‖ < a + δ :=
    hc.tendsto.eventually (eventually_lt_nhds hlt)
  have hz : chartExteriorCutoff e (a + δ) δ =ᶠ[𝓝 (e x)] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [e.open_target.mem_nhds hyt, hn] with z hzt hzn
    rw [chartExteriorCutoff, coordinateExtension_apply e _ hzt]
    have hzero : exteriorSphereCutoff (a + δ) δ (e.symm z) = 0 :=
      exteriorLayerProfile_eq_zero hδ hzn.le
    rw [hzero]
    ring
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hy

/-- Off the actual collar, the shifted cutoff is exactly the actual
exterior indicator, including the closed-ball boundary convention. -/
theorem shifted_chartExteriorCutoff_eq_indicator_off_collar
    (e : OpenPartialHomeomorph E M) {a δ : ℝ} (hδ : 0 < δ)
    (hs : closedBall (0 : E) (a + 2 * δ) ⊆ e.source)
    {y : M} (hy : y ∉ e '' sphereTraceAnnulus a (a + 2 * δ)) :
    chartExteriorCutoff e (a + δ) δ y =
      (e '' closedBall (0 : E) a)ᶜ.indicator (fun _ => (1 : ℝ)) y := by
  by_cases hyb : y ∈ e '' closedBall (0 : E) a
  · have ht : y ∉ tsupport (chartExteriorCutoff e (a + δ) δ) :=
      fun h => shifted_chartExteriorCutoff_tsupport_subset e hδ hs h hyb
    rw [image_eq_zero_of_notMem_tsupport ht, indicator_of_notMem (not_not.mpr hyb)]
  · have hout : y ∉ e '' closedBall (0 : E) (a + 2 * δ) := by
      rintro ⟨x, hx, rfl⟩
      have hn : ‖x‖ ≤ a + 2 * δ := by
        simpa only [mem_closedBall, dist_zero_right] using hx
      have hna : a < ‖x‖ := by
        apply lt_of_not_ge
        intro hh
        exact hyb ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hh, rfl⟩
      exact hy ⟨x, ⟨hna.le, hn⟩, rfl⟩
    have hs' : closedBall (0 : E) ((a + δ) + δ) ⊆ e.source := by
      simpa only [show a + δ + δ = a + 2 * δ by ring] using hs
    have hout' : y ∉ e '' closedBall (0 : E) ((a + δ) + δ) := by
      simpa only [show a + δ + δ = a + 2 * δ by ring] using hout
    rw [chartExteriorCutoff_eq_one_of_notMem_chart_ball e hδ hs' hout',
      indicator_of_mem hyb]

/-- The two-scale difference is supported in the union of the two
collars and has squared magnitude at most the sum of their indicators. -/
theorem shifted_chartExteriorCutoff_sub_sq_le
    (e : OpenPartialHomeomorph E M) {a δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hsδ : closedBall (0 : E) (a + 2 * δ) ⊆ e.source)
    (hsη : closedBall (0 : E) (a + 2 * η) ⊆ e.source) (y : M) :
    (chartExteriorCutoff e (a + δ) δ y - chartExteriorCutoff e (a + η) η y) ^ 2 ≤
      (e '' sphereTraceAnnulus a (a + 2 * δ)).indicator (fun _ => (1 : ℝ)) y +
      (e '' sphereTraceAnnulus a (a + 2 * η)).indicator (fun _ => (1 : ℝ)) y := by
  have hδr := chartExteriorCutoff_range e (a + δ) δ y
  have hηr := chartExteriorCutoff_range e (a + η) η y
  have hsq : (chartExteriorCutoff e (a + δ) δ y -
      chartExteriorCutoff e (a + η) η y) ^ 2 ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one _).mpr
    exact abs_le.mpr ⟨by linarith only [hδr.1, hηr.2],
      by linarith only [hδr.2, hηr.1]⟩
  by_cases hyδ : y ∈ e '' sphereTraceAnnulus a (a + 2 * δ) <;>
    by_cases hyη : y ∈ e '' sphereTraceAnnulus a (a + 2 * η)
  · simpa only [indicator_of_mem hyδ, indicator_of_mem hyη] using hsq.trans (by norm_num : (1 : ℝ) ≤ 1 + 1)
  · simpa only [indicator_of_mem hyδ, indicator_of_notMem hyη, add_zero] using hsq
  · simpa only [indicator_of_notMem hyδ, indicator_of_mem hyη, zero_add] using hsq
  · rw [shifted_chartExteriorCutoff_eq_indicator_off_collar e hδ hsδ hyδ,
      shifted_chartExteriorCutoff_eq_indicator_off_collar e hη hsη hyη, sub_self]
    simp only [zero_pow (by decide : 2 ≠ 0), indicator_of_notMem hyδ,
      indicator_of_notMem hyη, add_zero, le_refl]

#print axioms shifted_chartExteriorCutoff_tsupport_subset
#print axioms shifted_chartExteriorCutoff_eq_indicator_off_collar
#print axioms shifted_chartExteriorCutoff_sub_sq_le

end Yamabe3.Analysis.EuclideanSphereTrace
