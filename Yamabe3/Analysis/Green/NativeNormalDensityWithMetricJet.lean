import Yamabe3.Analysis.Green.NativeNormalDensity

/-!
# Retaining the original metric first jet in the same normalized chart

This stronger entry point uses the identical proved normalized-chart and
Gauss-extension construction. It retains the two original metric-jet
conclusions that the earlier density-only output omitted, together with
every previous output. Its witnesses can be carried unchanged through the
Green construction and into the actual end estimates. This is preservation
of already proved data, not a new Green or regularity theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Topology Matrix

namespace Yamabe3.Analysis.NormalCoordinates

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The same actual normalized chart and Gauss extension, retaining the
metric value and Christoffel first-jet conclusions for the original chart. -/
theorem exists_native_normalized_density_with_metricJet (g : RiemannianMetric n M) (p : M) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
      (r : ℝ) (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (D : LeviCivitaData gE),
      0 < r ∧ Metric.closedBall 0 r ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      g.pullbackCoefficients e 0 = innerSL ℝ ∧
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) 0 = 0 ∧
      (∀ x ∈ Metric.closedBall 0 r,
        gE.euclideanCoefficients x = g.pullbackCoefficients e x) ∧
      (∀ x w, gE.euclideanCoefficients x x w = inner ℝ x w) ∧
      ContDiff ℝ ∞ (gE.pullbackVolumeDensity id) ∧
      (∀ x, 0 < gE.pullbackVolumeDensity id x) ∧
      gE.pullbackVolumeDensity id 0 = 1 ∧
      fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0 ∧
      (∀ x ∈ Metric.closedBall 0 r,
        gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x) ∧
      g.pullbackVolumeDensity e 0 = 1 ∧
      fderiv ℝ (g.pullbackVolumeDensity e) 0 = 0 := by
  obtain ⟨e, he0, hep, he, hei, hGauss, hB0, hΓ0⟩ :=
    g.exists_normalized_exponential_chart_firstJet p
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  have hr : 0 < R / 4 := by positivity
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) (Metric.ball 0 R) :=
    fun x hx => (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (e.open_source.mem_nhds (hRU hx)))).contDiffWithinAt
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  obtain ⟨gE, D, hmetric, hglobalGauss⟩ :=
    CoordinateExponential.exists_gauss_metric_extension hr
      (by linarith : R / 4 < R / 2) (by linarith : R / 2 < R)
      (g.pullbackCoefficients e) hcoeff
      (fun x _ v w => g.symm (e x) _ _)
      (fun x hx v hv => by
        apply g.pos (e x)
        intro hz
        apply hv
        apply heD.mfderiv_injective (hRU hx)
        rw [map_zero]
        convert! hz using 1)
      (fun x hx => hGauss x (hRU hx))
  have hclosed : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R / 4) ⊆
      e.source := by
    intro x hx
    apply hRU
    exact (Metric.closedBall_subset_ball (by linarith : R / 4 < R)) hx
  have hmetricGerm : gE.euclideanCoefficients =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin n))]
      g.pullbackCoefficients e := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hr] with x hx
    exact hmetric x (Metric.ball_subset_closedBall hx)
  have hΓE : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients 0 = 0 := by
    have heq : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients 0 =
        CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) 0 := by
      unfold CoordinateExponential.christoffelBilinear
      rw [hmetricGerm.self_of_nhds, hmetricGerm.fderiv_eq]
    exact heq.trans hΓ0
  have hDE : fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0 :=
    fderiv_density_eq_zero_of_christoffel_eq_zero gE D 0 hΓE
  have hρeq (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ Metric.closedBall 0 (R / 4)) :
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x :=
    density_eq_of_coefficients_eq g gE e x (hmetric x hx)
  have hρGerm : gE.pullbackVolumeDensity id =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin n))]
      g.pullbackVolumeDensity e := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hr] with x hx
    exact hρeq x (Metric.ball_subset_closedBall hx)
  have hρ0 : g.pullbackVolumeDensity e 0 = 1 :=
    density_eq_one_of_coefficients_eq_inner g e 0 hB0
  obtain ⟨hρSmooth, hρPos⟩ := contDiff_pos_euclidean_density gE
  exact ⟨e, R / 4, gE, D, hr, hclosed, hep, he, hei, hB0, hΓ0, hmetric, hglobalGauss,
    hρSmooth, hρPos, hρGerm.self_of_nhds.trans hρ0, hDE, hρeq, hρ0,
    hρGerm.fderiv_eq.symm.trans hDE⟩

#print axioms exists_native_normalized_density_with_metricJet

end Yamabe3.Analysis.NormalCoordinates
