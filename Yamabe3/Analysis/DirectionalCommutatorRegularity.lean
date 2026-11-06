import Yamabe3.Analysis.DirectionalL2Calculus

/-! Tangential H2 of the same first derivative supplies the directional
derivative of every Hessian entry. This differentiates the actual scalar
commutator without assuming global H3 across a source jump. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem directional_hessian_of_first_H2
    {O : Set E} {u : E → ℝ} (hu : MemWkp 2 2 u O)
    (s i j : Fin d) (hs : MemWkp 2 2 (chosenWeakPartial' 2 s u O) O) :
    DirectionalL2 s (chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) O := by
  let p (k : Fin d) := chosenWeakPartial' 2 k u O
  let r := chosenWeakPartial' 2 i (p s) O
  have hp (k : Fin d) := (hu.chosenWeakPartial_mem k).memW1p
  have hwp (k : Fin d) := chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p k
  have hr : MemWkp 1 2 r O := hs.chosenWeakPartial_mem i
  have hpr : HasWeakPartialDeriv s r (p i) O :=
    weakPartial_commute s i (hwp s) (hwp i)
      (chosenWeakPartial'_isWeakPartial_of_mem hs.memW1p i)
  refine ⟨chosenWeakPartial'_memLp_of_mem (hp i) j,
    chosenWeakPartial' 2 j r O,chosenWeakPartial'_memLp_of_mem hr.memW1p j,?_⟩
  exact weakPartial_commute s j hpr (chosenWeakPartial'_isWeakPartial_of_mem (hp i) j)
    (chosenWeakPartial'_isWeakPartial_of_mem hr.memW1p j)

theorem directional_differentiated_source
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j,ContDiff ℝ ∞ (fun x => A x i j))
    {u r : E → ℝ} (hu : MemWkp 2 2 u O) (k s : Fin d)
    (hs : MemWkp 2 2 (chosenWeakPartial' 2 s u O) O) (hr : DirectionalL2 s r O) :
    DirectionalL2 s
      (differentiatedSource A (fun j => chosenWeakPartial' 2 j u O)
        (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k) O := by
  apply hr.add
  apply DirectionalL2.sum Finset.univ
  intro i _
  apply DirectionalL2.sum Finset.univ
  intro j _
  exact ((directional_hessian_of_first_H2 hu s i j hs).smooth_mul hO hOc
    (contDiff_partial (hA i j) k)).add
    ((directionalL2_of_memW1p (hu.chosenWeakPartial_mem j).memW1p s).smooth_mul hO hOc
      (contDiff_partial (contDiff_partial (hA i j) k) i))

#print axioms directional_hessian_of_first_H2
#print axioms directional_differentiated_source
end Yamabe3.Analysis.UniformElliptic
