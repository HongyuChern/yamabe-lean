import Yamabe3.Analysis.UniformElliptic.UniformCutoffCalculus
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Basic

/-!
# Explicit cutoff control by the genuine divergence source

The scalar source is the fixed upstream negative divergence of a(x) Du.
Its first coefficient-derivative term is bounded explicitly. Together with
the actual product formula this controls the principal operator of a cutoff
by source, solution and first-derivative energy with common numeric bounds.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem matrix_sq_sum_le_of_entry_bound
    (a : Matrix (Fin d) (Fin d) ℝ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i j, |a i j| ≤ A) :
    (∑ i : Fin d, ∑ j : Fin d, a i j ^ 2) ≤ (d : ℝ) ^ 2 * A ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).mpr (ha i j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private def coefficientDrift (a : E → Matrix (Fin d) (Fin d) ℝ)
    (u : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, partialDeriv i (fun y => a y i j) x * partialDeriv j u x

private theorem coefficientDrift_sq_le
    (a : E → Matrix (Fin d) (Fin d) ℝ) (u : E → ℝ) (x : E)
    {L : ℝ} (hL : 0 ≤ L)
    (hDa : ∀ i j : Fin d, |partialDeriv i (fun y => a y i j) x| ≤ L) :
    coefficientDrift a u x ^ 2 ≤ (d : ℝ) ^ 3 * L ^ 2 * gradientSq u x := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin d × Fin d))
    (fun p => partialDeriv p.1 (fun y => a y p.1 p.2) x)
    (fun p => partialDeriv p.2 u x)
  simp only [Fintype.sum_prod_type] at hCS
  have hsum := matrix_sq_sum_le_of_entry_bound
    (fun i j => partialDeriv i (fun y => a y i j) x) hL hDa
  have hgrad : (∑ i : Fin d, ∑ j : Fin d, partialDeriv j u x ^ 2) =
      (d : ℝ) * gradientSq u x := by
    simp only [gradientSq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hgrad] at hCS
  apply hCS.trans
  calc
    _ ≤ ((d : ℝ) ^ 2 * L ^ 2) * ((d : ℝ) * gradientSq u x) :=
      mul_le_mul_of_nonneg_right hsum (mul_nonneg (Nat.cast_nonneg d) (gradientSq_nonneg u x))
    _ = _ := by ring

/-- The principal part is controlled by the actual negative divergence
source and the true first derivatives, with an explicit coefficient bound. -/
theorem principalPart_sq_le_divergence_source
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (x : E)
    {L : ℝ} (hL : 0 ≤ L)
    (hDa : ∀ i j : Fin d, |partialDeriv i (fun y => a y i j) x| ≤ L) :
    principalPart a u x ^ 2 ≤ 2 * principalSource a u x ^ 2 +
      2 * (d : ℝ) ^ 3 * L ^ 2 * gradientSq u x := by
  have hid := principalSource_eq_secondOrderOperator (a := a)
    (fun _ _ => 0) ha hu x
  have hmain : secondOrderOperator a (fun _ _ => 0) u x = principalPart a u x := by
    simp [secondOrderOperator, principalPart]
  have hdrift : (∑ j : Fin d,
      ((0 : ℝ) - ∑ i : Fin d, partialDeriv i (fun y => a y i j) x) * partialDeriv j u x) =
      -coefficientDrift a u x := by
    simp only [zero_sub, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib, coefficientDrift]
    rw [Finset.sum_comm]
  rw [hmain, hdrift] at hid
  have hDrift := coefficientDrift_sq_le a u x hL hDa
  have hsplit : principalPart a u x ^ 2 ≤
      2 * principalSource a u x ^ 2 + 2 * coefficientDrift a u x ^ 2 := by
    have hp : principalPart a u x = -principalSource a u x - coefficientDrift a u x := by
      linarith
    rw [hp]
    nlinarith [sq_nonneg (principalSource a u x - coefficientDrift a u x)]
  nlinarith

/-- An explicit constant, with no selection depending on the coefficient
field or the solution. -/
def cutoffSourceEnergyConstant (d : ℕ) (A L N : ℝ) : ℝ :=
  max 8 (max (4 * (d : ℝ) ^ 2 * A ^ 2 * N)
    (8 * (d : ℝ) ^ 3 * L ^ 2 + 8 * (d : ℝ) ^ 2 * A ^ 2 * N))

theorem cutoffSourceEnergyConstant_nonneg (d : ℕ) (A L N : ℝ) :
    0 ≤ cutoffSourceEnergyConstant d A L N :=
  (by norm_num : (0 : ℝ) ≤ 8).trans (le_max_left _ _)

/-- The genuine cutoff principal source is bounded by genuine divergence
source, solution and gradient energies using only common coefficient bounds. -/
theorem principalPart_cutoff_sq_le_divergence_source
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {η u : E → ℝ} (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x : E)
    {A L N : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (haBound : ∀ i j : Fin d, |a x i j| ≤ A)
    (hDa : ∀ i j : Fin d, |partialDeriv i (fun y => a y i j) x| ≤ L)
    (hηx : |η x| ≤ 1) (hgη : gradientSq η x ≤ N) (hhη : hessianSq η x ≤ N) :
    principalPart a (fun y => η y * u y) x ^ 2 ≤
      cutoffSourceEnergyConstant d A L N *
        (principalSource a u x ^ 2 + u x ^ 2 + gradientSq u x) := by
  let K : ℝ := (d : ℝ) ^ 2 * A ^ 2
  let D : ℝ := (d : ℝ) ^ 3 * L ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcut := principalPart_mul_sq_le a hη hu x hK hN
    (matrix_sq_sum_le_of_entry_bound (a x) hA haBound) hηx hgη hhη
  have hsource := principalPart_sq_le_divergence_source ha hu x hL hDa
  have hsource' : principalPart a u x ^ 2 ≤
      2 * principalSource a u x ^ 2 + 2 * D * gradientSq u x := by
    simpa only [D, mul_assoc] using hsource
  let C := cutoffSourceEnergyConstant d A L N
  have hC₁ : (8 : ℝ) ≤ C := le_max_left _ _
  have hC₂ : 4 * K * N ≤ C := by
    have h : 4 * (d : ℝ) ^ 2 * A ^ 2 * N ≤ C :=
      (le_max_left _ _).trans (le_max_right _ _)
    simpa only [K, mul_assoc] using h
  have hC₃ : 8 * D + 8 * K * N ≤ C := by
    have h : 8 * (d : ℝ) ^ 3 * L ^ 2 + 8 * (d : ℝ) ^ 2 * A ^ 2 * N ≤ C :=
      (le_max_right _ _).trans (le_max_right _ _)
    simpa only [K, D, mul_assoc] using h
  apply hcut.trans
  calc
    _ ≤ 4 * ((2 * principalSource a u x ^ 2 + 2 * D * gradientSq u x) +
        K * N * u x ^ 2 + 2 * K * N * gradientSq u x) := by gcongr
    _ = 8 * principalSource a u x ^ 2 + 4 * K * N * u x ^ 2 +
        (8 * D + 8 * K * N) * gradientSq u x := by ring
    _ ≤ C * principalSource a u x ^ 2 + C * u x ^ 2 + C * gradientSq u x := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hC₁ (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hC₂ (sq_nonneg _)))
        (mul_le_mul_of_nonneg_right hC₃ (gradientSq_nonneg u x))
    _ = _ := by dsimp [C]; ring

#print axioms principalPart_sq_le_divergence_source
#print axioms principalPart_cutoff_sq_le_divergence_source

end Yamabe3.Analysis.UniformElliptic
