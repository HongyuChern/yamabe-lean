import Yamabe3.Analysis.UniformElliptic.ScaledPrincipalHessian
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients

/-!
# Uniform Hessian energy for the actual normalized metric coefficients

The coefficient array is the fixed upstream density-weighted inverse pullback
metric, with the identity parametrization of the actual Euclidean metric.
Its smoothness and value at zero are proved from native metric identities.
The normal-chart construction supplies the two displayed normalization
identities; no elliptic estimate or asymptotic decay is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The coefficient matrix is the actual retained divergence coefficient
array, not an unrelated elliptic operator. -/
def nativeDivergenceMatrix (g : RiemannianMetric 3 E) (x : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  divergenceCoefficients g (OpenPartialHomeomorph.refl E) x

theorem contDiff_nativeDivergenceMatrix (g : RiemannianMetric 3 E) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => nativeDivergenceMatrix g x i j) := by
  have h := contDiffOn_divergenceCoefficients (g := g) (OpenPartialHomeomorph.refl E)
    contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn i j
  exact contDiffOn_univ.mp h

/-- Actual metric and density normalization identify all entries at zero. -/
theorem nativeDivergenceMatrix_zero (g : RiemannianMetric 3 E)
    (hB : g.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0 = 1) : nativeDivergenceMatrix g 0 = 1 := by
  have hcoeff : g.pullbackCoefficients id 0 = g.euclideanCoefficients 0 := by
    ext v w
    change g.inner 0 (mfderiv (𝓡 3) (𝓡 3) id 0 v)
      (mfderiv (𝓡 3) (𝓡 3) id 0 w) = g.inner 0 v w
    rw [mfderiv_id]
    rfl
  have hinv : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).IsInvertible := by
    rw [← hB]
    exact g.inner_isInvertible 0
  have hbasis (j : Fin 3) : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
      (EuclideanSpace.single j 1) = EuclideanSpace.proj j := by
    ext v
    simp [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.single_apply]
  have hdual (j : Fin 3) : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).inverse
      (EuclideanSpace.proj j) = EuclideanSpace.single j 1 := by
    rw [← hbasis j]
    exact hinv.inverse_apply_self _
  ext i j
  change g.pullbackVolumeDensity id 0 * EuclideanSpace.proj i
    ((g.pullbackCoefficients id 0).inverse (EuclideanSpace.proj j)) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  rw [hρ, one_mul, hcoeff, hB, hdual]
  simp [Matrix.one_apply]

/-- The normal native Euclidean metric gives one radius and the same
numerical Hessian bound for every rescaling, on a fixed actual test ball. -/
theorem exists_uniform_native_rescaled_hessian_energy (g : RiemannianMetric 3 E)
    (hB : g.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0 = 1) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∀ u : E → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u ⊆ ball 0 R →
        (∫ x, hessianSq u x) ≤
          4 * (∫ x, principalPart (fun y => nativeDivergenceMatrix g (r • y)) u x ^ 2) :=
  exists_uniform_rescaled_hessian_energy
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).continuous)
    (nativeDivergenceMatrix_zero g hB hρ) hR

#print axioms contDiff_nativeDivergenceMatrix
#print axioms nativeDivergenceMatrix_zero
#print axioms exists_uniform_native_rescaled_hessian_energy

end Yamabe3.Analysis.UniformElliptic
