import GreenMass.GaussSphereGram
import GreenMass.NativeSphereDilation
import GreenMass.NativeSphereArea

/-!
# Native area of the actual radius sphere for a Gauss metric

The metric below is induced by the actual dilation into the supplied smooth
ambient metric.  The radial Gauss identity is imposed on that same metric,
only at the sphere in question.  Its native volume measure is proved equal
to the Euclidean radius-sphere measure weighted by the actual ambient volume
density.  The proof uses native Gram densities and change of metric, so it
does not assume a surface coarea formula or any orientation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GreenMass.NativeGaussSphereArea

open NativeSphereGeometry NativeSphereDilation

/-- The actual metric induced on the parametrized radius sphere by `g`. -/
def gaussRadiusMetric (g : RiemannianMetric 3 E) (r : ℝ) (hr : r ≠ 0) :
    RiemannianMetric 2 S :=
  RiemannianMetric.Induced.pullbackMetric g (SphereMeasure.dilation r)
    (smooth_dilation r) (immersion_dilation r hr)

theorem gaussRadiusMetric_inner (g : RiemannianMetric 3 E) (r : ℝ) (hr : r ≠ 0)
    (θ : S) (v w : TangentSpace (𝓡 2) θ) :
    (gaussRadiusMetric g r hr).inner θ v w =
      g.inner (SphereMeasure.dilation r θ)
        (mfderiv (𝓡 2) (𝓡 3) (SphereMeasure.dilation r) θ v)
        (mfderiv (𝓡 2) (𝓡 3) (SphereMeasure.dilation r) θ w) := rfl

theorem pullbackVolumeDensity_id (g : RiemannianMetric 3 E) (x : E) :
    g.pullbackVolumeDensity id x = g.tangentVolumeDensity x := by
  simp only [RiemannianMetric.pullbackVolumeDensity,
    RiemannianMetric.tangentVolumeDensity, id_eq, mfderiv_id,
    ContinuousLinearMap.id_apply]

theorem gaussRadiusMetric_tangentDensity
    (g : RiemannianMetric 3 E) (r : ℝ) (hr : r ≠ 0) (θ : S)
    (hGauss : ∀ w : E, g.inner (SphereMeasure.dilation r θ)
      (SphereMeasure.dilation r θ) w = inner ℝ (SphereMeasure.dilation r θ) w) :
    (gaussRadiusMetric g r hr).tangentVolumeDensity θ =
      g.pullbackVolumeDensity id (SphereMeasure.dilation r θ) *
        (radiusMetric r hr).tangentVolumeDensity θ := by
  let A : V →L[ℝ] E := mfderiv (𝓡 2) (𝓡 3) (SphereMeasure.dilation r) θ
  have horth (v : V) : inner ℝ (θ : E) (A v) = 0 := by
    change inner ℝ (θ : E)
      (mfderiv (𝓡 2) (𝓡 3) (SphereMeasure.dilation r) θ v) = 0
    rw [mfderiv_dilation, real_inner_smul_right, inner_normal_tangent, mul_zero]
  have hGauss' (w : E) : g.inner (SphereMeasure.dilation r θ) (θ : E) w =
      inner ℝ (θ : E) w := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (SphereMeasure.dilation r θ)
    have h := hGauss w
    change B (r • (θ : E)) w = inner ℝ (r • (θ : E)) w at h
    change B (θ : E) w = inner ℝ (θ : E) w
    apply mul_left_cancel₀ hr
    simpa only [map_smul, smul_apply, smul_eq_mul, real_inner_smul_left] using h
  have hdet : 0 ≤ (Matrix.of (fun i j : Fin 3 =>
      g.inner (SphereMeasure.dilation r θ)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j))).det :=
    (Real.sqrt_pos.mp (g.tangentVolumeDensity_pos (SphereMeasure.dilation r θ))).le
  have h := GaussSphereGram.sqrt_det_tangent_eq_ambient_mul_euclidean_gram
    (g.inner (SphereMeasure.dilation r θ)) A (θ : E)
    (norm_eq_of_mem_sphere θ) horth hGauss' hdet
  rw [pullbackVolumeDensity_id]
  change Real.sqrt (Matrix.of (fun i j : Fin 2 =>
      g.inner (SphereMeasure.dilation r θ)
        (A (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (A (EuclideanSpace.basisFun (Fin 2) ℝ j)))).det =
      Real.sqrt (Matrix.of (fun i j : Fin 3 =>
        g.inner (SphereMeasure.dilation r θ)
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j))).det *
      Real.sqrt (Matrix.of (fun i j : Fin 2 => inner ℝ
        (A (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (A (EuclideanSpace.basisFun (Fin 2) ℝ j)))).det
  simpa only [Matrix.gram] using! h

theorem gaussRadiusMetric_relativeDensity
    (g : RiemannianMetric 3 E) (r : ℝ) (hr : r ≠ 0) (θ : S)
    (hGauss : ∀ w : E, g.inner (SphereMeasure.dilation r θ)
      (SphereMeasure.dilation r θ) w = inner ℝ (SphereMeasure.dilation r θ) w) :
    (gaussRadiusMetric g r hr).relativeVolumeDensity (radiusMetric r hr) θ =
      g.pullbackVolumeDensity id (SphereMeasure.dilation r θ) := by
  unfold RiemannianMetric.relativeVolumeDensity
  rw [gaussRadiusMetric_tangentDensity g r hr θ hGauss,
    mul_div_cancel_right₀ _ ((radiusMetric r hr).tangentVolumeDensity_pos θ).ne']

/-- The actual induced sphere-area measure, relative to the actual Euclidean
induced radius metric. -/
theorem gaussRadiusMetric_volume_eq_withDensity
    (g : RiemannianMetric 3 E) (r : ℝ) (hr : r ≠ 0)
    (hGauss : ∀ (θ : S) (w : E), g.inner (SphereMeasure.dilation r θ)
      (SphereMeasure.dilation r θ) w = inner ℝ (SphereMeasure.dilation r θ) w) :
    (gaussRadiusMetric g r hr).volumeMeasure =
      (radiusMetric r hr).volumeMeasure.withDensity (fun θ : S =>
        ENNReal.ofReal (g.pullbackVolumeDensity id (SphereMeasure.dilation r θ))) := by
  rw [(gaussRadiusMetric g r hr).volumeMeasure_eq_withDensity_relativeVolumeDensity
    (radiusMetric r hr)]
  congr 1
  funext θ
  rw [gaussRadiusMetric_relativeDensity g r hr θ (hGauss θ)]

/-- `dσ_g(rθ) = ρ_g(rθ) r² dω`, proved for the same actual induced metric.
Here `dω` is Lebesgue's canonical polar measure, already identified with the
native induced unit-sphere area. -/
theorem gaussRadiusMetric_volume_eq_weighted_polarArea
    (g : RiemannianMetric 3 E) (r : ℝ) (hr : r ≠ 0)
    (hGauss : ∀ (θ : S) (w : E), g.inner (SphereMeasure.dilation r θ)
      (SphereMeasure.dilation r θ) w = inner ℝ (SphereMeasure.dilation r θ) w) :
    (gaussRadiusMetric g r hr).volumeMeasure =
      (ENNReal.ofReal (r ^ 2) • (volume : Measure E).toSphere).withDensity
        (fun θ : S =>
          ENNReal.ofReal (g.pullbackVolumeDensity id (SphereMeasure.dilation r θ))) := by
  rw [gaussRadiusMetric_volume_eq_withDensity g r hr hGauss, radiusMetric_volume,
    ← NativeSphereArea.sphereArea_eq_native_area]
  rfl

#print axioms gaussRadiusMetric_tangentDensity
#print axioms gaussRadiusMetric_volume_eq_withDensity
#print axioms gaussRadiusMetric_volume_eq_weighted_polarArea

end GreenMass.NativeGaussSphereArea
