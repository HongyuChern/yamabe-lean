import Yamabe3.Analysis.UniformElliptic.NativeScaledHessian
import Yamabe3.Analysis.UniformElliptic.UniformDivergenceHessian
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Radial

/-!
# The genuine density-weighted native Laplacian is the actual divergence source

No coordinate PDE is assumed. The fixed native metric gradient is its actual
inverse-metric dual, and its coefficient flux is expanded in the Euclidean
basis. The retained native divergence identity then gives the scalar source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem pullback_id_eq_inner (g : RiemannianMetric 3 E) (x : E) :
    g.pullbackCoefficients id x = g.euclideanCoefficients x := by
  ext v w
  change g.inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w) = g.inner x v w
  rw [mfderiv_id]
  rfl

private theorem mvfderiv_euclidean (u : E → ℝ) (x : E) :
    mvfderiv (𝓡 3) u x = fderiv ℝ u x := by
  ext v
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  rfl

/-- The true coefficient flux is exactly density times the native gradient. -/
theorem matrixFlux_native_eq_density_gradient
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (u : E → ℝ) (i : Fin 3) (x : E) :
    matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x =
      g.pullbackVolumeDensity id x * WithLp.ofLp (D.gradient u x) i := by
  classical
  have hp := sum_divergenceCoefficients_eq_inverse_pairing (g := g)
    (OpenPartialHomeomorph.refl E) x (fderiv ℝ u x) (EuclideanSpace.proj i)
  have hleft : (∑ k : Fin 3, ∑ j : Fin 3,
      divergenceCoefficients g (OpenPartialHomeomorph.refl E) x k j *
        (fderiv ℝ u x) (EuclideanSpace.single j 1) *
          (EuclideanSpace.proj i) (EuclideanSpace.single k 1)) =
      matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x := by
    simp [matrixFlux, nativeDivergenceMatrix, partialDeriv,
      mul_ite, Finset.sum_ite_irrel]
  rw [hleft] at hp
  change matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x =
    g.pullbackVolumeDensity id x * EuclideanSpace.proj i
      ((g.pullbackCoefficients id x).inverse (fderiv ℝ u x)) at hp
  rw [pullback_id_eq_inner] at hp
  have hgrad : (g.euclideanCoefficients x).inverse (fderiv ℝ u x) = D.gradient u x := by
    have hi : (g.euclideanCoefficients x).IsInvertible := by
      convert! g.inner_isInvertible x
    apply hi.inverse_apply_eq.mpr
    ext v
    change (fderiv ℝ u x) v = g.inner x (D.gradient u x) v
    rw [D.inner_gradient]
    exact congrArg (fun L => L v) (mvfderiv_euclidean u x).symm
  rw [hgrad] at hp
  simpa only [EuclideanSpace.proj, PiLp.proj_apply] using hp

/-- For every locally smooth actual scalar function, its native negative
Laplacian multiplied by native density equals the actual negative divergence. -/
theorem native_principalSource_eq_negative_density_laplacian
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ ∞ u x) :
    principalSource (nativeDivergenceMatrix g) u x =
      -g.pullbackVolumeDensity id x * D.laplacian u x := by
  have hflux (i : Fin 3) :
      (fun y : E => g.pullbackVolumeDensity id y * WithLp.ofLp (D.gradient u y) i) =
        matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i := by
    funext y
    exact (matrixFlux_native_eq_density_gradient g D u i y).symm
  have hd := D.density_mul_laplacian_eq_divergence hu
  simp_rw [hflux, EuclideanSpace.basisFun_apply] at hd
  change principalSource (nativeDivergenceMatrix g) u x = _
  change -(∑ i : Fin 3, partialDeriv i
    (matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i) x) = _
  change g.pullbackVolumeDensity id x * D.laplacian u x =
    ∑ i : Fin 3, partialDeriv i
      (matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i) x at hd
  linarith

#print axioms matrixFlux_native_eq_density_gradient
#print axioms native_principalSource_eq_negative_density_laplacian

end Yamabe3.Analysis.UniformElliptic
