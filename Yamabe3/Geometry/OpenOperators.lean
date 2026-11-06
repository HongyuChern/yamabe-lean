import Yamabe3.Geometry.OpenRestriction
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# Native scalar operators on the inherited open submanifold

The inclusion differential is derived from the already proved actual local
diffeomorphism. The metric is the retained restriction through that inclusion.
This connects ambient off-pole PDEs with the native punctured metric, without
supplying curvature or Laplacian equality as an extra interface premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Yamabe3.Geometry

open PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
/-- Off-boundary smoothness restricts to the inherited native atlas. -/
theorem contMDiff_restrict_of_contMDiffOn (O : Opens M) {u : M → ℝ}
    (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u O) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x : O => u x.val) := by
  intro x
  exact (hu.contMDiffAt (O.isOpen.mem_nhds x.property)).comp x
    (contMDiff_subtype_val (I := 𝓡 n) (U := O) (n := ∞) x)

/-- The actual Laplacian of the actual restricted metric is the ambient
Laplacian applied before restriction. -/
theorem laplacian_restrictMetric (g : RiemannianMetric n M) (O : Opens M)
    (D : LeviCivitaData g) (DO : LeviCivitaData (restrictMetric g O))
    {u : M → ℝ} {x : O} (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u x.val) :
    DO.laplacian (fun y : O => u y.val) x = D.laplacian u x.val := by
  apply DO.laplacian_comp_of_metric_pullback D
    (contMDiff_subtype_val (I := 𝓡 n) (U := O) (n := ∞) x) ?_ ?_ hu
  · exact Eventually.of_forall fun y =>
      ⟨(isLocalDiffeomorph_opens_val O y).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  · exact Eventually.of_forall fun y a b => rfl

/-- Scalar curvature also restricts through the actual inclusion. -/
theorem scalarCurvature_restrictMetric (g : RiemannianMetric n M) (O : Opens M)
    (D : LeviCivitaData g) (DO : LeviCivitaData (restrictMetric g O)) (x : O) :
    DO.scalarCurvature x = D.scalarCurvature x.val := by
  apply DO.scalarCurvature_eq_of_local_isometry D isOpen_univ
    (contMDiff_subtype_val (I := 𝓡 n) (U := O) (n := ∞)).contMDiffOn
    (fun y _ a b => rfl) (mem_univ x)

/-- The normalized conformal Laplacian has exactly the same value in the
ambient manifold and in the actual inherited open submanifold. -/
theorem conformalP_restrictMetric {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (O : Opens M) {u : M → ℝ} {x : O}
    (hu : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u x.val) :
    -(restrictMetric g O).leviCivitaData.laplacian (fun y : O => u y.val) x +
        ((restrictMetric g O).leviCivitaData.scalarCurvature x / 8) * u x.val =
      -g.leviCivitaData.laplacian u x.val +
        (g.leviCivitaData.scalarCurvature x.val / 8) * u x.val := by
  rw [laplacian_restrictMetric g O g.leviCivitaData (restrictMetric g O).leviCivitaData hu,
    scalarCurvature_restrictMetric g O g.leviCivitaData (restrictMetric g O).leviCivitaData x]

#print axioms contMDiff_restrict_of_contMDiffOn
#print axioms laplacian_restrictMetric
#print axioms scalarCurvature_restrictMetric
#print axioms conformalP_restrictMetric

end Yamabe3.Geometry
