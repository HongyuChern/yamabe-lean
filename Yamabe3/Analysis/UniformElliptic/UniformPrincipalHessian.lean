import Yamabe3.Analysis.UniformElliptic.EuclideanHessianEnergy

/-!
# An explicit Hessian bound uniform over coefficients close to identity

The coefficient field is an actual array multiplying the actual classical
second derivatives. Its squared distance to the identity is bounded only on
the support of the test function. Exact Euclidean energy, finite Cauchy--Schwarz
and absorption give the numerical constant 4 for every such field. There is no
constant selected after the coefficient field.

The finite contraction estimate follows the proof architecture of the fixed
PoincareLib `Analysis/Parabolic/WeakRegularity/Interior/VariableEnergy.lean`
(derived from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e,
Apache-2.0); here it is used directly on spatial Euclidean functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual nondivergence principal operator. -/
def principalPart (a : E → Matrix (Fin d) (Fin d) ℝ) (u : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, a x i j * partialDeriv i (partialDeriv j u) x

theorem continuous_principalPart
    {a : E → Matrix (Fin d) (Fin d) ℝ} (ha : ∀ i j, Continuous (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) : Continuous (principalPart a u) :=
  continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
    (ha i j).mul (contDiff_partial (contDiff_partial hu j) i).continuous))

theorem hasCompactSupport_principalPart
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u : E → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (principalPart a u) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hnot
  apply hx
  simp [principalPart, second_partial_eq_zero_of_notMem_tsupport hnot]

theorem integrable_principalPart_sq
    {a : E → Matrix (Fin d) (Fin d) ℝ} (ha : ∀ i j, Continuous (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Integrable (fun x => principalPart a u x ^ 2) volume := by
  have hm : MemLp (principalPart a u) 2 volume :=
    (continuous_principalPart ha hu).memLp_of_hasCompactSupport (hasCompactSupport_principalPart a hc)
  exact hm.integrable_sq

/-- The true Laplacian is the identity-coefficient contraction. -/
theorem principalPart_one (u : E → ℝ) (x : E) :
    principalPart (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) u x = euclideanLaplacian u x := by
  classical
  simp [principalPart, euclideanLaplacian, Matrix.one_apply]

private theorem principal_error_sq_le
    {a : E → Matrix (Fin d) (Fin d) ℝ} {u : E → ℝ} {ε : ℝ}
    (hosc : ∀ x ∈ tsupport u,
      (∑ i : Fin d, ∑ j : Fin d, (a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ ε ^ 2)
    (x : E) :
    principalPart (fun x => a x - 1) u x ^ 2 ≤ ε ^ 2 * hessianSq u x := by
  by_cases hx : x ∈ tsupport u
  · have hCS := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin d × Fin d))
      (fun p => a x p.1 p.2 - (1 : Matrix (Fin d) (Fin d) ℝ) p.1 p.2)
      (fun p => partialDeriv p.1 (partialDeriv p.2 u) x)
    simp only [Fintype.sum_prod_type] at hCS
    exact hCS.trans (mul_le_mul_of_nonneg_right (hosc x hx)
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))))
  · simp [principalPart, hessianSq, second_partial_eq_zero_of_notMem_tsupport hx]

/-- Quantitative absorption with an entirely explicit coefficient. The
inequality is valid even before imposing smallness on ε. -/
theorem principal_hessian_energy_absorption
    {a : E → Matrix (Fin d) (Fin d) ℝ} (ha : ∀ i j, Continuous (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {ε : ℝ}
    (hosc : ∀ x ∈ tsupport u,
      (∑ i : Fin d, ∑ j : Fin d, (a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ ε ^ 2) :
    (1 - 2 * ε ^ 2) * (∫ x, hessianSq u x) ≤ 2 * (∫ x, principalPart a u x ^ 2) := by
  have hH := integrable_hessianSq hu hc
  have hP := integrable_principalPart_sq ha hu hc
  have hE := integrable_principalPart_sq
    (a := fun x => a x - 1) (fun i j => (ha i j).sub continuous_const) hu hc
  have hbound : (∫ x, principalPart (fun y => a y - 1) u x ^ 2) ≤
      ε ^ 2 * (∫ x, hessianSq u x) := by
    rw [← integral_const_mul]
    exact integral_mono hE (hH.const_mul _) (principal_error_sq_le hosc)
  have hdecomp (x : E) : euclideanLaplacian u x =
      principalPart a u x - principalPart (fun y => a y - 1) u x := by
    rw [← principalPart_one u x]
    unfold principalPart
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hsplit : (∫ x, euclideanLaplacian u x ^ 2) ≤
      2 * (∫ x, principalPart a u x ^ 2) +
        2 * (∫ x, principalPart (fun y => a y - 1) u x ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hP.const_mul 2) (hE.const_mul 2)]
    apply integral_mono (integrable_euclideanLaplacian_sq hu hc)
      ((hP.const_mul 2).add (hE.const_mul 2))
    intro x
    dsimp only [Pi.add_apply]
    rw [hdecomp]
    nlinarith [sq_nonneg (principalPart a u x + principalPart (fun y => a y - 1) u x)]
  rw [integral_euclideanLaplacian_sq_eq_hessianSq hu hc] at hsplit
  nlinarith

/-- One numerical constant works for every continuous coefficient array
whose squared deviation from identity is at most one quarter on the support. -/
theorem principal_hessian_energy_le_four
    {a : E → Matrix (Fin d) (Fin d) ℝ} (ha : ∀ i j, Continuous (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hosc : ∀ x ∈ tsupport u,
      (∑ i : Fin d, ∑ j : Fin d, (a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) :
    (∫ x, hessianSq u x) ≤ 4 * (∫ x, principalPart a u x ^ 2) := by
  have h := principal_hessian_energy_absorption ha hu hc (ε := 1 / 2)
    (by intro x hx; have h := hosc x hx; norm_num at h ⊢; exact h)
  norm_num at h
  linarith

/-- In dimension three the explicit entrywise tolerance one sixth supplies
the previous squared matrix tolerance. -/
theorem principal_hessian_energy_le_four_three
    {a : EuclideanSpace ℝ (Fin 3) → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ∀ i j, Continuous (fun x => a x i j))
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hosc : ∀ x ∈ tsupport u, ∀ i j : Fin 3,
      |a x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 / 6) :
    (∫ x, hessianSq u x) ≤ 4 * (∫ x, principalPart a u x ^ 2) := by
  apply principal_hessian_energy_le_four ha hu hc
  intro x hx
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (1 / 6 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 1 / 6)).mpr (hosc x hx i j)
    _ = 1 / 4 := by norm_num

#print axioms principal_hessian_energy_absorption
#print axioms principal_hessian_energy_le_four
#print axioms principal_hessian_energy_le_four_three

end Yamabe3.Analysis.UniformElliptic
