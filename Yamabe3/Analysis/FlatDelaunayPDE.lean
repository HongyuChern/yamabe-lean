import Yamabe3.Analysis.NativeRadialLaplacian
import Yamabe3.Analysis.DelaunayRadialProfile
import Yamabe3.Geometry.OpenOperators
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean

/-!
# The constructed Delaunay profile solves the literal flat native PDE

The metric below is the native Euclidean inner product, with its canonical
Levi-Civita connection.  The flat curvature and density identities are proved
from those definitions.  Restriction to any open subset avoiding the origin
retains the same Laplacian.  No spherical existence theorem is used here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace Yamabe3.Analysis.Delaunay

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem euclideanMetric_connection_const {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.connection (fun _ => v) x u = 0 := by
  rw [D.connection_const_eq_inverse]
  change (innerSL ℝ).inverse (metricKoszulCovector
    (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ) x) u v) = 0
  simp [metricKoszulCovector]

theorem euclideanMetric_curvatureTensor {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))
    (x u v w z : EuclideanSpace ℝ (Fin n)) :
    D.curvatureTensor x u v w z = 0 := by
  have he (a b : EuclideanSpace ℝ (Fin n)) :
      D.euclideanConnection a b = fun _ => 0 := by
    funext y
    exact euclideanMetric_connection_const D y a b
  unfold LeviCivitaData.curvatureTensor
  rw [D.curvature_eq_euclideanConnection]
  simp only [he, fderiv_const_apply, ContinuousLinearMap.zero_apply, add_zero,
    sub_self, RiemannianMetric.euclideanMetric_inner, inner_zero_left]

theorem euclideanMetric_scalarCurvature {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))
    (x : EuclideanSpace ℝ (Fin n)) : D.scalarCurvature x = 0 := by
  simp [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci,
    euclideanMetric_curvatureTensor]

theorem euclideanMetric_density {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    (RiemannianMetric.euclideanMetric n).pullbackVolumeDensity id x = 1 := by
  classical
  unfold RiemannianMetric.pullbackVolumeDensity
  simp only [mfderiv_id, RiemannianMetric.euclideanMetric_inner]
  change Real.sqrt (Matrix.of (fun i j : Fin n =>
    inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))).det = 1
  simp only [(EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite]
  change Real.sqrt (1 : Matrix (Fin n) (Fin n) ℝ).det = 1
  simp

theorem flat_radialProfile_smooth {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (τ : ℝ) {x : E3} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y : E3 => radialProfile v τ ‖y‖) x := by
  exact (((radialProfile_contDiffOn hv τ).contDiffAt
    (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).comp x
    (contDiffAt_norm ℝ hx)).contMDiffAt

/-- The `div grad` Laplacian of the actual flat metric, with no residual. -/
theorem flat_radialProfile_equation {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4)
    (τ : ℝ) {x : E3} (hx : x ≠ 0) :
    -8 * (RiemannianMetric.euclideanMetric 3).leviCivitaData.laplacian
      (fun y : E3 => radialProfile v τ ‖y‖) x =
      6 * radialProfile v τ ‖x‖ ^ 5 := by
  have hd : (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity id =
      fun _ => (1 : ℝ) := funext euclideanMetric_density
  rw [Yamabe3.Analysis.GreenParametrix.native_laplacian_radial
    (RiemannianMetric.euclideanMetric 3) (by intro y w; rfl)
    (radialProfile v τ) (radialProfile_contDiffOn hv τ) hx, hd]
  simpa using radialProfile_radial_equation hv hODE τ (norm_pos_iff.mpr hx)

/-- This equation is on the inherited open metric and its canonical
connection, rather than an ambient or coordinate replacement. -/
theorem flat_radialProfile_restricted_equation
    (O : TopologicalSpace.Opens E3) (hO : ∀ x : O, (x : E3) ≠ 0)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hODE : ∀ t, deriv (deriv v) t = v t / 4 - 3 * v t ^ 5 / 4)
    (τ : ℝ) (x : O) :
    let g := Yamabe3.Geometry.restrictMetric (RiemannianMetric.euclideanMetric 3) O;
    -8 * g.leviCivitaData.laplacian
      (fun y : O => radialProfile v τ ‖(y : E3)‖) x +
      g.leviCivitaData.scalarCurvature x * radialProfile v τ ‖(x : E3)‖ =
      6 * radialProfile v τ ‖(x : E3)‖ ^ 5 := by
  dsimp only
  rw [Yamabe3.Geometry.laplacian_restrictMetric
      (RiemannianMetric.euclideanMetric 3) O _ _
      (flat_radialProfile_smooth hv τ (hO x)),
    Yamabe3.Geometry.scalarCurvature_restrictMetric
      (RiemannianMetric.euclideanMetric 3) O
      (RiemannianMetric.euclideanMetric 3).leviCivitaData _ x,
    euclideanMetric_scalarCurvature, zero_mul, add_zero]
  exact flat_radialProfile_equation hv hODE τ (hO x)

theorem flat_radialProfile_restricted_smooth
    (O : TopologicalSpace.Opens E3) (hO : ∀ x : O, (x : E3) ≠ 0)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (τ : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y : O => radialProfile v τ ‖(y : E3)‖) := by
  intro x
  exact (flat_radialProfile_smooth hv τ (hO x)).comp x
    (contMDiff_subtype_val (I := 𝓡 3) (U := O) (n := ∞) x)

#print axioms flat_radialProfile_equation
#print axioms flat_radialProfile_restricted_equation

end Yamabe3.Analysis.Delaunay
