import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.Gauss.NormalizedChart
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence

/-!
# The native first volume-density jet in normalized exponential coordinates

The coordinates in the main existence theorem are obtained from the actual
metric and point.  Its global Euclidean metric is the proved cutoff extension
of their actual pullback metric, agreeing on a smaller closed ball.  Its
positive smooth density is the square root of that metric's Gram determinant.

The vanishing first density jet is deduced from the actual Levi-Civita
connection and its trace formula.  No normal-coordinate or density jet is an
extra input to the existence theorem.  The identification of this coordinate
density with the intrinsic volume measure is not asserted by this module.
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

/-- Equal actual pullback coefficients have equal actual Gram densities. -/
theorem density_eq_of_coefficients_eq
    (g : RiemannianMetric n M)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (h : gE.euclideanCoefficients x = g.pullbackCoefficients e x) :
    gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x := by
  unfold RiemannianMetric.pullbackVolumeDensity
  congr 1
  congr 1
  ext i j
  simp only [Matrix.of_apply, id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
  exact congrArg (fun B => B (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)) h

/-- An orthonormal actual pullback coefficient matrix has density one. -/
theorem density_eq_one_of_coefficients_eq_inner
    (g : RiemannianMetric n M)
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (h : g.pullbackCoefficients e x = innerSL ℝ) :
    g.pullbackVolumeDensity e x = 1 := by
  have hmatrix : Matrix.of (fun i j : Fin n =>
      g.pullbackCoefficients e x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [h]
    ext i j
    change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) = if i = j then 1 else 0
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j
  change Real.sqrt (Matrix.of (fun i j : Fin n =>
      g.pullbackCoefficients e x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j))).det = 1
  rw [hmatrix, Matrix.det_one, Real.sqrt_one]

/-- A vanishing actual Christoffel tensor forces the first density derivative
to vanish by the native connection-trace identity. -/
theorem fderiv_density_eq_zero_of_christoffel_eq_zero
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData gE)
    (x : EuclideanSpace ℝ (Fin n))
    (hΓ : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients x = 0) :
    fderiv ℝ (gE.pullbackVolumeDensity id) x = 0 := by
  have hconnection (u v : EuclideanSpace ℝ (Fin n)) :
      D.euclideanConnection u v x = 0 := by
    calc
      D.euclideanConnection u v x =
          CoordinateExponential.christoffelBilinear gE.euclideanCoefficients x u v :=
        D.connection_const_eq_inverse x u v
      _ = 0 := by rw [hΓ]; rfl
  ext v
  rw [D.fderiv_density_eq_connection_trace]
  simp only [hconnection, PiLp.zero_apply, Finset.sum_const_zero, mul_zero,
    ContinuousLinearMap.zero_apply]

/-- The actual volume density of a global smooth Euclidean metric is smooth
and everywhere positive. -/
theorem contDiff_pos_euclidean_density
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ ∞ (gE.pullbackVolumeDensity id) ∧
      ∀ x, 0 < gE.pullbackVolumeDensity id x := by
  have h (x : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (gE.pullbackVolumeDensity id) x ∧
        0 < gE.pullbackVolumeDensity id x := by
    apply gE.contDiffAt_pullbackVolumeDensity contMDiffAt_id
    intro a b hab
    rw [mfderiv_id] at hab
    change a = b at hab
    exact hab
  exact ⟨contDiff_iff_contDiffAt.mpr (fun x => (h x).1), fun x => (h x).2⟩

/-- Every smooth Riemannian metric at every point supplies a genuine
normalized exponential chart and a global Gauss extension.  The actual
densities agree on a nonzero closed ball, are normalized to one at its center,
and have vanishing first derivative there. -/
theorem exists_native_normalized_density (g : RiemannianMetric n M) (p : M) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
      (r : ℝ) (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (D : LeviCivitaData gE),
      0 < r ∧ Metric.closedBall 0 r ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
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
  exact ⟨e, R / 4, gE, D, hr, hclosed, hep, he, hei, hmetric, hglobalGauss,
    hρSmooth, hρPos, hρGerm.self_of_nhds.trans hρ0, hDE, hρeq, hρ0,
    hρGerm.fderiv_eq.symm.trans hDE⟩

#print axioms density_eq_of_coefficients_eq
#print axioms density_eq_one_of_coefficients_eq_inner
#print axioms fderiv_density_eq_zero_of_christoffel_eq_zero
#print axioms contDiff_pos_euclidean_density
#print axioms exists_native_normalized_density

end Yamabe3.Analysis.NormalCoordinates
