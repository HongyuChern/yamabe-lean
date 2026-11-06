import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Separation.Basic

noncomputable section
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Yamabe3.W6

/-- The literal finite complement used by Target.puncturedOpen, defined
here without importing the target's global geodesic implementation. -/
def euclideanPuncturedOpen : Opens (EuclideanSpace ℝ (Fin 3)) := by
  classical
  exact ⟨(({0} : Finset (EuclideanSpace ℝ (Fin 3))) : Set _)ᶜ,
    ({0} : Finset (EuclideanSpace ℝ (Fin 3))).finite_toSet.isClosed.isOpen_compl⟩

@[simp] theorem mem_euclideanPuncturedOpen (z : EuclideanSpace ℝ (Fin 3)) :
    z ∈ euclideanPuncturedOpen ↔ z ≠ 0 := by
  classical
  simp [euclideanPuncturedOpen]

#print axioms mem_euclideanPuncturedOpen

end Yamabe3.W6
