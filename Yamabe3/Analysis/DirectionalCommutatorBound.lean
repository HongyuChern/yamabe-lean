import Yamabe3.Analysis.WeakDivergenceOperatorContinuity
import Yamabe3.Analysis.DirectionalPieceRecovery
import Yamabe3.Analysis.BoundaryNormalHessianBound

/-! The differentiated source has an actual L2 bound with only the
specified source derivative. A discontinuous source need not be globally H1. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem differentiatedSource_eq_weak_commutator_ae {O : Set E} (hO : IsOpen O)
    (a : E → Matrix (Fin d) (Fin d) ℝ) (k : Fin d)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (r : E → ℝ) :
    differentiatedSource a (fun j => chosenWeakPartial' 2 j u O)
      (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k =ᵐ[volume.restrict O]
      fun x => r x-weakDivergenceSource O (fun x i j => partialDeriv k (fun y => a y i j) x) u x := by
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr
    (fun j => chosen_weak_hessian_commute_ae hO hu j i))] with x hx
  simp only [differentiatedSource, weakDivergenceSource, hx, sub_neg_eq_add]

theorem exists_explicit_directional_source_bound {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) (k : Fin d) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ u r : E → ℝ, MemWkp 2 2 u O → MemLp r 2 (volume.restrict O) →
      iteratedWeakSobolevNorm 0 2
        (differentiatedSource a (fun j => chosenWeakPartial' 2 j u O)
          (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O) r k) O ≤
        iteratedWeakSobolevNorm 0 2 r O+C*iteratedWeakSobolevNorm 2 2 u O := by
  let da : E → Matrix (Fin d) (Fin d) ℝ := fun x i j => partialDeriv k (fun y => a y i j) x
  obtain ⟨C,hC,hb⟩ := exists_weakDivergenceSource_bound hO hOc da
    (fun i j => contDiff_partial (ha i j) k)
  refine ⟨C,hC,?_⟩
  intro u r hu hr
  rw [wkpNorm_congr_ae (k:=0) (by norm_num) hO (differentiatedSource_eq_weak_commutator_ae hO a k hu r)]
  exact (sobolevNorm_sub_le (k:=0) hO hr (hb u hu).1).trans (add_le_add le_rfl (hb u hu).2)

#print axioms differentiatedSource_eq_weak_commutator_ae
#print axioms exists_explicit_directional_source_bound
end Yamabe3.Analysis.UniformElliptic
