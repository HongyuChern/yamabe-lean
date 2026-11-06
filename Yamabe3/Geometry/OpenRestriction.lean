import PoincareLib.Geometry.Riemannian.Metric.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Restricting an actual metric to an open submanifold

`TopologicalSpace.Opens M` carries Mathlib's restricted atlas of an arbitrary
charted manifold `M`. This is different from placing a singleton chart on an
open subset of the model space. The inclusion is a local diffeomorphism for
these inherited smooth structures, so the native metric pullback is defined.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Yamabe3.Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Inclusion of an open subset of an arbitrary smooth manifold, with the
inherited atlas, is a smooth local diffeomorphism. Empty open sets are allowed. -/
theorem isLocalDiffeomorph_opens_val (O : Opens M) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (Subtype.val : O → M) := by
  classical
  intro x
  letI : Nonempty O := ⟨x⟩
  let e : OpenPartialHomeomorph O M :=
    O.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  have hinv : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff O e.symm y).mp
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  let d : PartialDiffeomorph (𝓡 n) (𝓡 n) O M ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun :=
        (contMDiff_subtype_val (I := 𝓡 n) (U := O) (n := ∞)).contMDiffOn
      contMDiffOn_invFun := hinv }
  refine ⟨d, ?_, ?_⟩
  · change x ∈ e.source
    simp [e]
  · intro y _
    rfl

/-- The restriction has the actual pullback bilinear form under inclusion. -/
noncomputable def restrictMetric (g : PoincareMT.RiemannianMetric n M)
    (O : Opens M) : PoincareMT.RiemannianMetric n O :=
  g.pullbackOfLocalDiffeomorph Subtype.val (isLocalDiffeomorph_opens_val O)

@[simp] theorem restrictMetric_inner (g : PoincareMT.RiemannianMetric n M)
    (O : Opens M) (x : O) (v w : TangentSpace (𝓡 n) x) :
    (restrictMetric g O).inner x v w = g.inner x.val
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : O → M) x v)
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : O → M) x w) := rfl

end Yamabe3.Geometry
