import GreenMass.NativeSphereGeometry
import PoincareLib.Geometry.Riemannian.Measure.RelativeDensity.Measure

/-!
# Native area under the actual radius dilation

The radius metric is induced by the actual map `θ ↦ R θ` into Euclidean
space. Its volume scales by `R²`, proved from the native tangent Gram
density and the upstream change-of-metric theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GreenMass.NativeSphereDilation

open NativeSphereGeometry

theorem smooth_dilation (R : ℝ) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (SphereMeasure.dilation R) := by
  change ContMDiff (𝓡 2) (𝓡 3) ∞ (fun θ : S => R • (θ : E))
  exact (show ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun _ : S => R) from
    contMDiff_const).smul smooth_inclusion

theorem mfderiv_dilation (R : ℝ) (θ : S) (v : TangentSpace (𝓡 2) θ) :
    mfderiv (𝓡 2) (𝓡 3) (SphereMeasure.dilation R) θ v =
      R • mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v := by
  change mvfderiv (𝓡 2) (fun p : S => R • (p : E)) θ v =
    R • mvfderiv (𝓡 2) (Subtype.val : S → E) θ v
  rw [mvfderiv_fun_smul mdifferentiableAt_const
    (smooth_inclusion.mdifferentiable (by simp) θ)]
  simp [mvfderiv_const]

theorem immersion_dilation (R : ℝ) (hR : R ≠ 0) (θ : S) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (SphereMeasure.dilation R) θ) := by
  intro v w h
  apply immersion_inclusion θ
  apply smul_right_injective E hR
  simpa only [mfderiv_dilation] using h

/-- The actual Euclidean induced metric of the radius-`R` sphere, expressed
on its unit-sphere parametrization. -/
def radiusMetric (R : ℝ) (hR : R ≠ 0) : RiemannianMetric 2 S :=
  RiemannianMetric.Induced.pullbackMetric euclideanMetric (SphereMeasure.dilation R)
    (smooth_dilation R) (immersion_dilation R hR)

theorem radiusMetric_inner (R : ℝ) (hR : R ≠ 0) (θ : S)
    (v w : TangentSpace (𝓡 2) θ) :
    (radiusMetric R hR).inner θ v w = R ^ 2 * sphereMetric.inner θ v w := by
  change inner ℝ (mvfderiv (𝓡 2) (SphereMeasure.dilation R) θ v)
    (mvfderiv (𝓡 2) (SphereMeasure.dilation R) θ w) =
      R ^ 2 * inner ℝ (mvfderiv (𝓡 2) (Subtype.val : S → E) θ v)
        (mvfderiv (𝓡 2) (Subtype.val : S → E) θ w)
  have hh (u : TangentSpace (𝓡 2) θ) :
      mvfderiv (𝓡 2) (SphereMeasure.dilation R) θ u =
        R • mvfderiv (𝓡 2) (Subtype.val : S → E) θ u := mfderiv_dilation R θ u
  rw [hh v, hh w, real_inner_smul_left, real_inner_smul_right]
  ring

theorem radiusMetric_tangentDensity (R : ℝ) (hR : R ≠ 0) (θ : S) :
    (radiusMetric R hR).tangentVolumeDensity θ =
      R ^ 2 * sphereMetric.tangentVolumeDensity θ := by
  have hm : (Matrix.of (fun i j : Fin 2 => (radiusMetric R hR).inner θ
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j))) =
      R ^ 2 • (Matrix.of (fun i j : Fin 2 => sphereMetric.inner θ
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j))) := by
    ext i j
    exact radiusMetric_inner R hR θ _ _
  unfold RiemannianMetric.tangentVolumeDensity
  rw [hm, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (sq_nonneg (R ^ 2)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sq_nonneg R)]

theorem radiusMetric_relativeDensity (R : ℝ) (hR : R ≠ 0) (θ : S) :
    (radiusMetric R hR).relativeVolumeDensity sphereMetric θ = R ^ 2 := by
  unfold RiemannianMetric.relativeVolumeDensity
  rw [radiusMetric_tangentDensity,
    mul_div_cancel_right₀ _ (sphereMetric.tangentVolumeDensity_pos θ).ne']

/-- The `R²` area factor follows from actual induced metrics and their native
volume measures, independently of the polar cone convention. -/
theorem radiusMetric_volume (R : ℝ) (hR : R ≠ 0) :
    (radiusMetric R hR).volumeMeasure =
      ENNReal.ofReal (R ^ 2) • sphereMetric.volumeMeasure := by
  rw [(radiusMetric R hR).volumeMeasure_eq_withDensity_relativeVolumeDensity sphereMetric]
  simp only [radiusMetric_relativeDensity]
  exact withDensity_const _

#print axioms mfderiv_dilation
#print axioms radiusMetric_inner
#print axioms radiusMetric_volume

end GreenMass.NativeSphereDilation
