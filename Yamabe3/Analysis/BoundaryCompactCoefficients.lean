import PoincareLib.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients

/-! Coefficient constants are chosen from a fixed compact set and elliptic
form before any source or weak solution. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.NirenbergEuclidean
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_compact_finite_family_bound {I : Type*} [Fintype I]
    {K : Set E} (hK : IsCompact K) (a : I → E → ℝ) (ha : ∀ i, Continuous (a i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ i, |a i x| ≤ C := by
  classical
  choose c hc using fun i => hK.exists_bound_of_continuousOn (ha i).continuousOn
  refine ⟨∑ i, max (c i) 0, Finset.sum_nonneg (fun i _ => le_max_right _ _), ?_⟩
  intro x hx i
  exact (by simpa only [Real.norm_eq_abs] using hc i x hx : |a i x| ≤ c i) |>.trans
    ((le_max_left _ _).trans (Finset.single_le_sum (fun j _ => le_max_right (c j) 0)
      (Finset.mem_univ i)))

/-- Fixed geometry gives finite bounds for the coefficients and the first
coefficient derivatives occurring in the actual weak Hessian equation. -/
theorem exists_compact_elliptic_coefficient_bounds [NeZero d]
    (B : SmoothEllipticBilinearForm d univ) {K : Set E} (hK : IsCompact K) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ x ∈ K, ∀ i j, |B.a x i j| ≤ C) ∧
      (∀ x ∈ K, ∀ i j,
        |fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)| ≤ D) := by
  obtain ⟨C, hC, ha⟩ := exists_compact_finite_family_bound hK
    (fun ij : Fin d × Fin d => fun x => B.a x ij.1 ij.2)
    (fun ij => B.continuous_a ij.1 ij.2)
  obtain ⟨D, hD, hb⟩ := exists_compact_finite_family_bound hK
    (fun ij : Fin d × Fin d => fun x =>
      fderiv ℝ (fun y => B.a y ij.1 ij.2) x (EuclideanSpace.single ij.1 1))
    (fun ij => ((B.smooth_a ij.1 ij.2).continuous_fderiv (by simp)).clm_apply continuous_const)
  exact ⟨C, D, hC, hD, fun x hx i j => ha x hx (i,j), fun x hx i j => hb x hx (i,j)⟩

#print axioms exists_compact_finite_family_bound
#print axioms exists_compact_elliptic_coefficient_bounds
end Yamabe3.Analysis.UniformElliptic
