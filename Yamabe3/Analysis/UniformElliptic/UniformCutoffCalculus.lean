import Yamabe3.Analysis.UniformElliptic.UniformPrincipalHessian

/-! # Actual cutoff calculus for the uniform Hessian estimate -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Squared Euclidean norm of the actual classical coordinate gradient. -/
def gradientSq (u : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, (partialDeriv i u x) ^ 2

/-- The actual mixed principal pairing. -/
def mixedPart (a : E → Matrix (Fin d) (Fin d) ℝ) (f g : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, a x i j * partialDeriv i f x * partialDeriv j g x

theorem gradientSq_nonneg (u : E → ℝ) (x : E) : 0 ≤ gradientSq u x :=
  Finset.sum_nonneg (fun _i _ => sq_nonneg _)

theorem hessianSq_nonneg (u : E → ℝ) (x : E) : 0 ≤ hessianSq u x :=
  Finset.sum_nonneg (fun _i _ => Finset.sum_nonneg (fun _j _ => sq_nonneg _))

theorem continuous_gradientSq {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (gradientSq u) :=
  continuous_finsetSum _ (fun i _ => (contDiff_partial hu i).continuous.pow 2)

theorem continuous_hessianSq {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (hessianSq u) :=
  continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
    (contDiff_partial (contDiff_partial hu j) i).continuous.pow 2))

private theorem partial_mul {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    partialDeriv i (fun x => f x * g x) =
      fun x => f x * partialDeriv i g x + g x * partialDeriv i f x := by
  funext x
  unfold partialDeriv
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem partial_add {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    partialDeriv i (fun x => f x + g x) = fun x => partialDeriv i f x + partialDeriv i g x := by
  funext x
  unfold partialDeriv
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

private theorem second_partial_mul {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i j : Fin d) (x : E) :
    partialDeriv i (partialDeriv j (fun y => f y * g y)) x =
      f x * partialDeriv i (partialDeriv j g) x +
        g x * partialDeriv i (partialDeriv j f) x +
        partialDeriv i f x * partialDeriv j g x +
        partialDeriv i g x * partialDeriv j f x := by
  rw [partial_mul hf hg j,
    partial_add (hf.mul (contDiff_partial hg j)) (hg.mul (contDiff_partial hf j)) i]
  rw [partial_mul hf (contDiff_partial hg j) i, partial_mul hg (contDiff_partial hf j) i]
  dsimp only
  ring

/-- The full classical product formula, without assuming matrix symmetry. -/
theorem principalPart_mul
    (a : E → Matrix (Fin d) (Fin d) ℝ) {η u : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x : E) :
    principalPart a (fun y => η y * u y) x =
      η x * principalPart a u x + u x * principalPart a η x +
        mixedPart a η u x + mixedPart a u η x := by
  have hterm (i j : Fin d) :
      a x i j * partialDeriv i (partialDeriv j (fun y => η y * u y)) x =
        η x * (a x i j * partialDeriv i (partialDeriv j u) x) +
          u x * (a x i j * partialDeriv i (partialDeriv j η) x) +
          a x i j * partialDeriv i η x * partialDeriv j u x +
          a x i j * partialDeriv i u x * partialDeriv j η x := by
    rw [second_partial_mul hη hu]
    ring
  unfold principalPart mixedPart
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem principalPart_sq_le_frobenius
    (a : E → Matrix (Fin d) (Fin d) ℝ) (u : E → ℝ) (x : E) :
    principalPart a u x ^ 2 ≤
      (∑ i : Fin d, ∑ j : Fin d, a x i j ^ 2) * hessianSq u x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin d × Fin d)) (fun p => a x p.1 p.2)
    (fun p => partialDeriv p.1 (partialDeriv p.2 u) x)
  simpa only [Fintype.sum_prod_type, principalPart, hessianSq] using h

theorem mixedPart_sq_le_frobenius
    (a : E → Matrix (Fin d) (Fin d) ℝ) (f g : E → ℝ) (x : E) :
    mixedPart a f g x ^ 2 ≤
      (∑ i : Fin d, ∑ j : Fin d, a x i j ^ 2) * (gradientSq f x * gradientSq g x) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin d × Fin d)) (fun p => a x p.1 p.2)
    (fun p => partialDeriv p.1 f x * partialDeriv p.2 g x)
  simp only [Fintype.sum_prod_type] at h
  have hsq : (∑ i : Fin d, ∑ j : Fin d,
      (partialDeriv i f x * partialDeriv j g x) ^ 2) = gradientSq f x * gradientSq g x := by
    simp only [gradientSq, mul_pow, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hterm : (∑ i : Fin d, ∑ j : Fin d, a x i j * (partialDeriv i f x * partialDeriv j g x)) =
      mixedPart a f g x := by simp only [mixedPart, mul_assoc]
  rw [hterm, hsq] at h
  exact h

private theorem sq_add_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

/-- A fully quantitative cutoff error bound with common coefficient and
cutoff derivative energies; it contains no chosen elliptic constant. -/
theorem principalPart_mul_sq_le
    (a : E → Matrix (Fin d) (Fin d) ℝ) {η u : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x : E)
    {K N : ℝ} (hK : 0 ≤ K) (_hN : 0 ≤ N)
    (hcoeff : (∑ i : Fin d, ∑ j : Fin d, a x i j ^ 2) ≤ K)
    (hηx : |η x| ≤ 1) (hgη : gradientSq η x ≤ N) (hhη : hessianSq η x ≤ N) :
    principalPart a (fun y => η y * u y) x ^ 2 ≤
      4 * (principalPart a u x ^ 2 + K * N * u x ^ 2 + 2 * K * N * gradientSq u x) := by
  have hpη : principalPart a η x ^ 2 ≤ K * N :=
    (principalPart_sq_le_frobenius a η x).trans
      (mul_le_mul hcoeff hhη (hessianSq_nonneg η x) hK)
  have hm₁ : mixedPart a η u x ^ 2 ≤ K * N * gradientSq u x := by
    apply (mixedPart_sq_le_frobenius a η u x).trans
    calc
      _ ≤ K * (N * gradientSq u x) :=
        mul_le_mul hcoeff (mul_le_mul_of_nonneg_right hgη (gradientSq_nonneg u x))
          (mul_nonneg (gradientSq_nonneg η x) (gradientSq_nonneg u x)) hK
      _ = _ := by ring
  have hm₂ : mixedPart a u η x ^ 2 ≤ K * N * gradientSq u x := by
    apply (mixedPart_sq_le_frobenius a u η x).trans
    calc
      _ ≤ K * (gradientSq u x * N) :=
        mul_le_mul hcoeff (mul_le_mul_of_nonneg_left hgη (gradientSq_nonneg u x))
          (mul_nonneg (gradientSq_nonneg u x) (gradientSq_nonneg η x)) hK
      _ = _ := by ring
  have hηsq : η x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hηx
  have hfirst : (η x * principalPart a u x) ^ 2 ≤ principalPart a u x ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) hηsq
  have hsecond : (u x * principalPart a η x) ^ 2 ≤ K * N * u x ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right hpη (sq_nonneg _)
  rw [principalPart_mul a hη hu]
  exact (sq_add_four_le _ _ _ _).trans (by nlinarith)

#print axioms principalPart_mul
#print axioms principalPart_sq_le_frobenius
#print axioms mixedPart_sq_le_frobenius
#print axioms principalPart_mul_sq_le

end Yamabe3.Analysis.UniformElliptic
