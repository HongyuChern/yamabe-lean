import Yamabe3.Analysis.HalfSpaceTangentialSource
import Yamabe3.Analysis.BoundaryWeakSourceBootstrap

/-! The first two tangential source derivatives are constructed from the
actual H2 functions on the two sides. The source traces need not agree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem twoSidedHalfSource_positive (f g : E → ℝ) {x : E} (hx : x∈halfSpace d) :
    twoSidedHalfSource f g x=f x := by
  simp only [twoSidedHalfSource,Pi.add_apply,indicator_of_mem hx,
    reflectedSample_zero_on_positive _ _ _ hx,add_zero]

theorem twoSidedHalfSource_first_tangential {f g : E → ℝ}
    (hf : MemW1p 2 f (halfSpace d)) (hg : MemW1p 2 g (halfSpace d))
    (i : Fin d) (hi : i≠0) :
    let r := twoSidedHalfSource (chosenWeakPartial' 2 i f (halfSpace d))
      (chosenWeakPartial' 2 i g (halfSpace d))
    MemLp r 2 volume ∧ HasWeakPartialDeriv i r (twoSidedHalfSource f g) univ := by
  exact ⟨memLp_twoSidedHalfSource (chosenWeakPartial'_memLp_of_mem hf i)
      (chosenWeakPartial'_memLp_of_mem hg i),
    weakPartial_twoSidedHalfSource i hi hf.1 hg.1
      (chosenWeakPartial'_memLp_of_mem hf i) (chosenWeakPartial'_memLp_of_mem hg i)
      (chosenWeakPartial'_isWeakPartial_of_mem hf i) (chosenWeakPartial'_isWeakPartial_of_mem hg i)⟩

theorem twoSidedHalfSource_second_tangential {f g : E → ℝ}
    (hf : MemWkp 2 2 f (halfSpace d)) (hg : MemWkp 2 2 g (halfSpace d))
    (i j : Fin d) (hi : i≠0) (hj : j≠0) :
    let r := twoSidedHalfSource (chosenWeakPartial' 2 i f (halfSpace d))
      (chosenWeakPartial' 2 i g (halfSpace d))
    let q := twoSidedHalfSource
      (chosenWeakPartial' 2 j (chosenWeakPartial' 2 i f (halfSpace d)) (halfSpace d))
      (chosenWeakPartial' 2 j (chosenWeakPartial' 2 i g (halfSpace d)) (halfSpace d))
    MemLp r 2 volume ∧ HasWeakPartialDeriv i r (twoSidedHalfSource f g) univ ∧
      MemLp q 2 volume ∧ HasWeakPartialDeriv j q r univ := by
  have h1 := twoSidedHalfSource_first_tangential hf.memW1p hg.memW1p i hi
  have h2 := twoSidedHalfSource_first_tangential (hf.chosenWeakPartial_mem i).memW1p
    (hg.chosenWeakPartial_mem i).memW1p j hj
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

#print axioms twoSidedHalfSource_positive
#print axioms twoSidedHalfSource_first_tangential
#print axioms twoSidedHalfSource_second_tangential
end Yamabe3.Analysis.UniformElliptic
