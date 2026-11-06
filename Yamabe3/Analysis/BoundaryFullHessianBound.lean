import Yamabe3.Analysis.BoundaryNormalHessianBound
import Yamabe3.Analysis.BoundaryCompactCoefficients

/-! Full weak Hessian bounds from tangential bounds, using the actual
nondivergence identity and mixed weak derivative uniqueness. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- All mixed components except (0,0) are controlled by the tangential
estimate for the same weak Hessian; no replacement function is chosen. -/
theorem off_normal_hessian_bound {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (M : ℝ≥0∞)
    (ht : ∀ k : Fin d, k ≠ 0 → ∀ i : Fin d,
      eLpNorm (chosenWeakPartial' 2 k (chosenWeakPartial' 2 i u O) O)
        2 (volume.restrict O) ≤ M) :
    ∀ ij : Fin d × Fin d, ij ≠ (0,0) →
      eLpNorm (chosenWeakPartial' 2 ij.1 (chosenWeakPartial' 2 ij.2 u O) O)
        2 (volume.restrict O) ≤ M := by
  intro ij hij
  by_cases hi : ij.1 = 0
  · have hj : ij.2 ≠ 0 := fun hj => hij (Prod.ext hi hj)
    rw [eLpNorm_congr_ae (chosen_weak_hessian_commute_ae hO hu ij.1 ij.2)]
    exact ht ij.2 hj ij.1
  · exact ht ij.1 hi ij.2

/-- Coefficient constants are fixed before the weak solution and source.
This controls the full Hessian, including the recovered normal component. -/
theorem exists_uniform_hessian_bound_from_tangential
    (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (u f : E → ℝ), MemWkp 2 2 u O → MemLp f 2 (volume.restrict O) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) →
      ∀ M : ℝ≥0∞,
      (∀ k : Fin d, k ≠ 0 → ∀ i : Fin d,
        eLpNorm (chosenWeakPartial' 2 k (chosenWeakPartial' 2 i u O) O)
          2 (volume.restrict O) ≤ M) →
      ∀ i j : Fin d,
        eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O)
          2 (volume.restrict O) ≤
        M + ENNReal.ofReal B.lam⁻¹ *
          (eLpNorm f 2 (volume.restrict O) + ENNReal.ofReal C * ((d : ℝ≥0∞) * d * M) +
            ENNReal.ofReal D * ∑ ij : Fin d × Fin d,
              eLpNorm (chosenWeakPartial' 2 ij.2 u O) 2 (volume.restrict O)) := by
  classical
  obtain ⟨C, D, hC, hD, ha, hb⟩ := exists_compact_elliptic_coefficient_bounds B hOc
  refine ⟨C, D, hC, hD, ?_⟩
  intro u f hu hf heq M ht i j
  have hoff := off_normal_hessian_bound hO hu M ht
  have hsum : (∑ ij ∈ (Finset.univ : Finset (Fin d × Fin d)).erase (0,0),
      eLpNorm (chosenWeakPartial' 2 ij.1 (chosenWeakPartial' 2 ij.2 u O) O) 2 (volume.restrict O)) ≤
        (d : ℝ≥0∞) * d * M := by
    calc
      _ ≤ ∑ ij ∈ (Finset.univ : Finset (Fin d × Fin d)).erase (0,0), M :=
        Finset.sum_le_sum fun ij hij => hoff ij (Finset.mem_erase.mp hij).1
      _ ≤ ∑ _ij : Fin d × Fin d, M :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => zero_le)
      _ = _ := by simp [Nat.cast_mul, mul_assoc]
  by_cases hij : (i,j) = (0,0)
  · have hi : i = 0 := congrArg Prod.fst hij
    have hj : j = 0 := congrArg Prod.snd hij
    subst i; subst j
    have hn := normal_weak_hessian_eLpNorm_bound B hO hOc C D hC hD
      (fun x hx => ha x (subset_closure hx)) (fun x hx => hb x (subset_closure hx)) hu hf heq
    exact (hn.trans (by gcongr)).trans (le_add_left (le_refl _))
  · exact (hoff (i,j) hij).trans (le_add_right (le_refl _))

#print axioms off_normal_hessian_bound
#print axioms exists_uniform_hessian_bound_from_tangential
end Yamabe3.Analysis.UniformElliptic
