import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The absolute determinant of the actual polar differential

For a unit vector orthogonal to a two-dimensional tangent differential,
the three-dimensional map with radial column equal to that unit vector and
tangential columns multiplied by `r` has absolute determinant `r²` times
the tangential Gram density. The result concerns ordinary native linear
maps and their actual determinant, with no measure convention supplied.
-/

noncomputable section
set_option autoImplicit false

namespace GreenMass.PolarGramJacobian

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev V := EuclideanSpace ℝ (Fin 2)

theorem abs_det_eq_sqrt_gram (L : E →L[ℝ] E) :
    |L.det| = Real.sqrt (Matrix.gram ℝ
      (fun i : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ i))).det := by
  have hs : |L.det| ^ 2 = (Matrix.gram ℝ
      (fun i : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ i))).det := by
    simpa [LinearMap.normDet_eq_norm_det, Real.norm_eq_abs] using
      L.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 3) ℝ)
  rw [← hs, Real.sqrt_sq_eq_abs, abs_abs]

theorem abs_det_polar_columns (L : E →L[ℝ] E) (A : V →L[ℝ] E)
    (θ : E) (r : ℝ) (hθ : ‖θ‖ = 1)
    (horth : ∀ v : V, inner ℝ θ (A v) = 0)
    (hzero : L (EuclideanSpace.basisFun (Fin 3) ℝ 0) = θ)
    (hsucc : ∀ i : Fin 2, L (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      r • A (EuclideanSpace.basisFun (Fin 2) ℝ i)) :
    |L.det| = r ^ 2 * Real.sqrt (Matrix.gram ℝ
      (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
  have hfirst : L (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
      r • A (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by simpa using hsucc 0
  have hsecond : L (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
      r • A (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by simpa using hsucc 1
  have hunit : inner ℝ θ θ = 1 := by
    rw [real_inner_self_eq_norm_sq, hθ]
    norm_num
  have horth' (v : V) : inner ℝ (A v) θ = 0 := by
    rw [real_inner_comm, horth]
  have hgram : (Matrix.gram ℝ
      (fun i : Fin 3 => L (EuclideanSpace.basisFun (Fin 3) ℝ i))).det =
      (r ^ 2) ^ 2 * (Matrix.gram ℝ
        (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp only [Matrix.gram_apply, hzero, hfirst, hsecond,
      real_inner_smul_left, real_inner_smul_right, hunit, horth, horth']
    ring
  rw [abs_det_eq_sqrt_gram, hgram, Real.sqrt_mul (sq_nonneg (r ^ 2)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg r)]

#print axioms abs_det_eq_sqrt_gram
#print axioms abs_det_polar_columns

end GreenMass.PolarGramJacobian
