import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# The actual tangential Gram density of a radial Gauss metric

In a three-dimensional vector space, a bilinear form with the radial Gauss
identity has tangential determinant equal to its ambient determinant times
the Euclidean tangential Gram determinant.  The radial vector is genuinely
unit and the two tangent columns are genuinely Euclidean orthogonal to it.
No orientation, preselected tangent basis, or surface-measure identity is
assumed.  The square-root identity is the algebraic input for the area
measure of the actual induced radius-sphere metric.
-/

noncomputable section
set_option autoImplicit false

namespace GreenMass.GaussSphereGram

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev V := EuclideanSpace ℝ (Fin 2)

theorem det_bilinear_columns (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    (Matrix.of (fun i j : Fin 3 => B
      (L (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (L (EuclideanSpace.basisFun (Fin 3) ℝ j)))).det =
      L.det ^ 2 * (Matrix.of (fun i j : Fin 3 => B
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j))).det := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let T : E →ₗ[ℝ] E := L.toLinearMap
  let β := B.toBilinForm
  have hB : Matrix.of (fun i j : Fin 3 => B
      (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      (LinearMap.BilinForm.toMatrix b) β := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hBT : Matrix.of (fun i j : Fin 3 => B
      (L (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (L (EuclideanSpace.basisFun (Fin 3) ℝ j))) =
      (LinearMap.BilinForm.toMatrix b) (β.comp T T) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [hB, hBT, LinearMap.BilinForm.toMatrix_comp b b,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
  change L.det * ((LinearMap.BilinForm.toMatrix b) β).det * L.det = _
  ring

theorem det_tangent_eq_ambient_mul_euclidean_gram
    (B : E →L[ℝ] E →L[ℝ] ℝ) (A : V →L[ℝ] E) (θ : E)
    (hθ : ‖θ‖ = 1) (horth : ∀ v : V, inner ℝ θ (A v) = 0)
    (hGauss : ∀ w : E, B θ w = inner ℝ θ w) :
    (Matrix.of (fun i j : Fin 2 => B
      (A (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (A (EuclideanSpace.basisFun (Fin 2) ℝ j)))).det =
      (Matrix.of (fun i j : Fin 3 => B
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j))).det *
      (Matrix.gram ℝ
        (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
  let columns : Fin 3 → E :=
    Fin.cons θ (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))
  let L : E →L[ℝ] E := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constrL columns
  have hzero : L (EuclideanSpace.basisFun (Fin 3) ℝ 0) = θ := by
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constrL columns
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis 0) = θ
    rw [Module.Basis.constrL_basis]
    rfl
  have hsucc (i : Fin 2) : L (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      A (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constrL columns
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i.succ) = _
    rw [Module.Basis.constrL_basis]
    rfl
  have hfirst : L (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
      A (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by simpa using hsucc 0
  have hsecond : L (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
      A (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by simpa using hsucc 1
  have hunit : inner ℝ θ θ = 1 := by
    rw [real_inner_self_eq_norm_sq, hθ]
    norm_num
  have hBblock : (Matrix.of (fun i j : Fin 3 => B
      (L (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (L (EuclideanSpace.basisFun (Fin 3) ℝ j)))).det =
      (Matrix.of (fun i j : Fin 2 => B
        (A (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (A (EuclideanSpace.basisFun (Fin 2) ℝ j)))).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp only [Matrix.of_apply, hzero, hfirst, hsecond, hGauss, hunit, horth]
    ring
  have heblock : (Matrix.gram ℝ
      (fun i : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ i))).det =
      (Matrix.gram ℝ
        (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp only [Matrix.gram_apply, hzero, hfirst, hsecond, hunit, horth]
    ring
  have hdet : L.det ^ 2 = (Matrix.gram ℝ
      (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
    rw [← heblock]
    simpa [LinearMap.normDet_eq_norm_det, Real.norm_eq_abs, sq_abs] using
      L.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 3) ℝ)
  rw [← hBblock, det_bilinear_columns, hdet, mul_comm]

theorem sqrt_det_tangent_eq_ambient_mul_euclidean_gram
    (B : E →L[ℝ] E →L[ℝ] ℝ) (A : V →L[ℝ] E) (θ : E)
    (hθ : ‖θ‖ = 1) (horth : ∀ v : V, inner ℝ θ (A v) = 0)
    (hGauss : ∀ w : E, B θ w = inner ℝ θ w)
    (hdet : 0 ≤ (Matrix.of (fun i j : Fin 3 => B
      (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j))).det) :
    Real.sqrt (Matrix.of (fun i j : Fin 2 => B
      (A (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (A (EuclideanSpace.basisFun (Fin 2) ℝ j)))).det =
      Real.sqrt (Matrix.of (fun i j : Fin 3 => B
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j))).det *
      Real.sqrt (Matrix.gram ℝ
        (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
  rw [det_tangent_eq_ambient_mul_euclidean_gram B A θ hθ horth hGauss,
    Real.sqrt_mul hdet]

#print axioms det_bilinear_columns
#print axioms det_tangent_eq_ambient_mul_euclidean_gram
#print axioms sqrt_det_tangent_eq_ambient_mul_euclidean_gram

end GreenMass.GaussSphereGram
