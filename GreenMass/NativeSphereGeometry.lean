import GreenMass.SphereMeasure
import PoincareLib.Geometry.Riemannian.Measure.Coarea.ImmersionDensity
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The native induced metric and outward normal of the Euclidean unit sphere

The metric is constructed from the actual smooth inclusion into Euclidean
three-space.  Its immersion property and its tangent space are proved by
Mathlib's sphere atlas.  No surface measure identification is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric PoincareMT
open scoped Manifold ContDiff Bundle

namespace GreenMass.NativeSphereGeometry

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev V := EuclideanSpace ℝ (Fin 2)
abbrev S := SphereMeasure.UnitSphere

instance : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp⟩

/-- The actual Euclidean Riemannian metric in the fixed three-dimensional model. -/
def euclideanMetric : RiemannianMetric 3 E :=
  { riemannianMetricVectorSpace E with
    contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top }

theorem smooth_inclusion : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S → E) :=
  contMDiff_coe_sphere

theorem immersion_inclusion (θ : S) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ) := by
  convert! injective_mvfderiv_subtypeVal_sphere θ

/-- The native induced Riemannian metric, using the actual inclusion differential. -/
def sphereMetric : RiemannianMetric 2 S :=
  RiemannianMetric.Induced.pullbackMetric euclideanMetric (Subtype.val : S → E)
    smooth_inclusion immersion_inclusion

theorem sphereMetric_inner (θ : S) (v w : TangentSpace (𝓡 2) θ) :
    sphereMetric.inner θ v w = inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v)
      (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ w) := rfl

/-- Native sphere coordinate density is the Gram determinant of its actual
ambient coordinate derivatives. -/
theorem sphereMetric_density {e : V → S} {x : V}
    (he : MDifferentiableAt (𝓡 2) (𝓡 2) e x) :
    sphereMetric.pullbackVolumeDensity e x =
      Real.sqrt (Matrix.of (fun i j : Fin 2 => inner ℝ
        (fderiv ℝ ((Subtype.val : S → E) ∘ e) x (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ ((Subtype.val : S → E) ∘ e) x (EuclideanSpace.basisFun (Fin 2) ℝ j)))).det := by
  rw [sphereMetric, RiemannianMetric.pullbackVolumeDensity_induced _ _ _ _ he]
  unfold RiemannianMetric.parametrizedVolumeDensity
  rw [mfderiv_eq_fderiv]
  rfl

/-- The inclusion differential takes values in the actual Euclidean normal
orthogonal complement. -/
theorem inner_normal_tangent (θ : S) (v : TangentSpace (𝓡 2) θ) :
    inner ℝ (θ : E) (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v) = 0 := by
  have hr : (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ).range =
      (ℝ ∙ (θ : E))ᗮ := by
    convert! range_mvfderiv_subtypeVal θ
  have hm : mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v ∈
      (ℝ ∙ (θ : E))ᗮ := by
    rw [← hr]
    exact ⟨v, rfl⟩
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hm)

/-- The unit normal points outwards: moving distance `t ≥ 0` in this direction
increases the Euclidean radius from `1` to `1+t`. -/
theorem outward_unit_normal (θ : S) :
    ‖(θ : E)‖ = 1 ∧
      (∀ v : TangentSpace (𝓡 2) θ,
        inner ℝ (θ : E) (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) θ v) = 0) ∧
      ∀ t : ℝ, 0 ≤ t → ‖(θ : E) + t • (θ : E)‖ = 1 + t := by
  refine ⟨norm_eq_of_mem_sphere θ, inner_normal_tangent θ, ?_⟩
  intro t ht
  have hadd : (θ : E) + t • (θ : E) = (1 + t) • (θ : E) := by
    rw [add_smul, one_smul]
  rw [hadd, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), norm_eq_of_mem_sphere θ, mul_one]

#print axioms immersion_inclusion
#print axioms sphereMetric_density
#print axioms inner_normal_tangent
#print axioms outward_unit_normal

end GreenMass.NativeSphereGeometry
