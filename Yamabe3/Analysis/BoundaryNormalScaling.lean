import Yamabe3.Analysis.NativeWeakDilation
import PoincareLib.Analysis.Sobolev.Boundary.Extension.Reflection

/-! Exact normal-coordinate scaling, including its determinant and volume
factor. Tangential coordinates are fixed, so the map fixes the boundary
face pointwise. This is preparation for a finite higher-order reflection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def normalFactor (r : ℝ) (i : Fin d) : ℝ := if i = 0 then r else 1

def normalScalingLinear (r : ℝ) : E →ₗ[ℝ] E where
  toFun x := WithLp.toLp 2 (fun i => normalFactor r i * x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

@[simp] theorem normalScalingLinear_apply (r : ℝ) (x : E) (i : Fin d) :
    normalScalingLinear r x i = normalFactor r i * x i := rfl

def normalScaling (r : ℝ) (hr : r ≠ 0) : E ≃L[ℝ] E :=
  ({ toLinearMap := normalScalingLinear r
     invFun := normalScalingLinear r⁻¹
     left_inv := by
       intro x; ext i; by_cases hi : i = 0 <;> simp [normalFactor, hi, hr, ← mul_assoc]
     right_inv := by
       intro x; ext i; by_cases hi : i = 0 <;> simp [normalFactor, hi, hr, ← mul_assoc]
     } : E ≃ₗ[ℝ] E).toContinuousLinearEquiv

@[simp] theorem normalScaling_apply (r : ℝ) (hr : r ≠ 0) (x : E) (i : Fin d) :
    normalScaling r hr x i = normalFactor r i * x i := rfl

@[simp] theorem normalScaling_symm_apply (r : ℝ) (hr : r ≠ 0) (x : E) (i : Fin d) :
    (normalScaling r hr).symm x i = normalFactor r⁻¹ i * x i := rfl

theorem normalScaling_single (r : ℝ) (hr : r ≠ 0) (i : Fin d) :
    normalScaling r hr (EuclideanSpace.single i 1) =
      normalFactor r i • EuclideanSpace.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst j; simp
  · simp [EuclideanSpace.single_apply, Pi.single_apply, hj]

theorem normalScaling_face (r : ℝ) (hr : r ≠ 0) (x : E) (hx : x 0 = 0) :
    normalScaling r hr x = x := by
  ext i
  by_cases hi : i = 0
  · subst i; simp [normalFactor, hx]
  · simp [normalFactor, hi]

theorem normalScaling_det (r : ℝ) : LinearMap.det (normalScalingLinear (d := d) r) = r := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hm : LinearMap.toMatrix b b (normalScalingLinear r) = Matrix.diagonal (normalFactor r) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    change normalFactor r i * (EuclideanSpace.single j 1 : E) i = _
    by_cases h : i = j
    · subst j; simp
    · simp [EuclideanSpace.single_apply, Pi.single_apply, h, Matrix.diagonal_apply]
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal]
  simp [normalFactor]

theorem map_volume_normalScaling (r : ℝ) (hr : r ≠ 0) :
    Measure.map (normalScaling (d := d) r hr) volume = ENNReal.ofReal |r⁻¹| • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
    (show LinearMap.det (normalScalingLinear r) ≠ 0 by rw [normalScaling_det]; exact hr)
  have heq : (normalScaling r hr : E → E) = normalScalingLinear r := by
    funext x; ext i; rfl
  rw [heq]
  simpa only [normalScaling_det] using h

theorem integral_normalScaling (r : ℝ) (hr : r ≠ 0) (f : E → ℝ) :
    (∫ x, f (normalScaling r hr x)) = |r⁻¹| * ∫ x, f x := by
  have he : MeasurableEmbedding (normalScaling (d := d) r hr) :=
    (normalScaling r hr).toHomeomorph.measurableEmbedding
  rw [← he.integral_map f,
    map_volume_normalScaling, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

#print axioms normalScaling_det
#print axioms map_volume_normalScaling
#print axioms integral_normalScaling
end Yamabe3.Analysis.UniformElliptic
