import PoincareLib.Topology.Manifold.CountableComplement
import PoincareLib.Geometry.Riemannian.Distance.Basic

/-!
# Connectivity and finite distance after finite punctures

The fixed upstream theorem proves path connectedness after countable deletion
in any connected topological manifold of dimension at least two. Specializing
its model dimension `1 + 2` to three covers every prescribed finite set. The
native Riemannian distance is then finite, independently of completeness.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Yamabe3.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [ConnectedSpace M]

/-- Deleting any finite set from a connected three-manifold leaves a
path-connected set. Neither smoothness, compactness nor orientation is needed. -/
theorem isPathConnected_finset_compl (Λ : Finset M) :
    IsPathConnected (Λ : Set M)ᶜ :=
  Poincare.Topology.Manifold.isPathConnected_compl_countable
    (n := 1) Λ.finite_toSet.countable

/-- The inherited open manifold with exactly these punctures is path connected. -/
theorem pathConnectedSpace_of_finset_complement
    (Λ : Finset M) (O : Opens M) (hO : (O : Set M) = (Λ : Set M)ᶜ) :
    PathConnectedSpace O := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  rw [hO]
  exact isPathConnected_finset_compl Λ

/-- Preconnectedness for the actual punctured open subtype. -/
theorem preconnectedSpace_of_finset_complement
    (Λ : Finset M) (O : Opens M) (hO : (O : Set M) = (Λ : Set M)ᶜ) :
    PreconnectedSpace O := by
  let : PathConnectedSpace O := pathConnectedSpace_of_finset_complement Λ O hO
  infer_instance

variable [T3Space M] [IsManifold (𝓡 3) ∞ M]

/-- Every native smooth Riemannian metric on this punctured manifold has
finite actual intrinsic distances. This uses connectivity, not completeness. -/
theorem edist_ne_top_of_finset_complement
    (Λ : Finset M) (O : Opens M) (hO : (O : Set M) = (Λ : Set M)ᶜ)
    (g : PoincareMT.RiemannianMetric 3 O) (x y : O) :
    g.edist x y ≠ ⊤ := by
  let : PreconnectedSpace O := preconnectedSpace_of_finset_complement Λ O hO
  exact g.edist_ne_top x y

end Yamabe3.Geometry
