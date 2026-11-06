import Yamabe3.Analysis.UniformElliptic.NativeScaledHessian
import Yamabe3.Analysis.UniformElliptic.UniformInteriorHessian
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual uniformly elliptic rescaled native coefficients

The density-weighted inverse metric is not supplied as an abstract family.
Its genuine smooth entries, symmetry and identity value construct all the
rescaled bilinear forms. A finite compact bound on the original coefficient
jets gives common rescaled bounds; near-identity control gives the explicit
ellipticity constant 1/2 before any scale is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.Weak

private def quadraticForm {d : ℕ} (a : Matrix (Fin d) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, ∑ j, a i j * v i * v j

private theorem quadraticForm_inner {d : ℕ} (a : Matrix (Fin d) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    quadraticForm a v = inner ℝ v (matMulE a v) := by
  change quadraticForm a v = (a.mulVec v.ofLp) ⬝ᵥ star v.ofLp
  simp only [quadraticForm, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Frobenius distance at most one half from identity gives the explicit
coercivity constant one half for the actual matrix action. -/
theorem coercive_of_frobenius_le_quarter {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℝ)
    (ha : (∑ i : Fin d, ∑ j : Fin d,
      (a i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4)
    (v : EuclideanSpace ℝ (Fin d)) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ v (matMulE a v) := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin d × Fin d))
    (fun p => a p.1 p.2 - (1 : Matrix (Fin d) (Fin d) ℝ) p.1 p.2)
    (fun p => v p.1 * v p.2)
  simp only [Fintype.sum_prod_type] at hCS
  have hfactor : (∑ i : Fin d, ∑ j : Fin d, (v i * v j) ^ 2) = ‖v‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [mul_pow, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have herror : quadraticForm (a - 1) v ^ 2 ≤ (1 / 4 : ℝ) * (‖v‖ ^ 2 * ‖v‖ ^ 2) := by
    apply (show quadraticForm (a - 1) v ^ 2 ≤
      (∑ i : Fin d, ∑ j : Fin d, (a i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) *
        (∑ i : Fin d, ∑ j : Fin d, (v i * v j) ^ 2) from by
          simpa only [quadraticForm, Matrix.sub_apply, mul_assoc] using hCS).trans
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right ha (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have habs : |quadraticForm (a - 1) v| ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [herror]
  have hone : quadraticForm (1 : Matrix (Fin d) (Fin d) ℝ) v = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [quadraticForm, Matrix.one_apply, pow_two]
  have hdecomp : quadraticForm a v = quadraticForm (a - 1) v + ‖v‖ ^ 2 := by
    rw [← hone]
    simp only [quadraticForm, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [← quadraticForm_inner, hdecomp]
  have h := (abs_le.mp habs).1
  linarith

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem frobenius_le_quarter_of_entry_bound (a : Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j, |a i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 / 6) :
    (∑ i : Fin 3, ∑ j : Fin 3, (a i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2) ≤ 1 / 4 := by
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (1 / 6 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 1 / 6)).mpr (ha i j)
    _ = _ := by norm_num

/-- Common original compact coefficient bounds control every nonnegative
rescaling of size at most one, through any prescribed finite order. -/
theorem exists_common_rescaled_coefficient_jets
    {a : E → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) (k : ℕ) {R : ℝ} (_hR : 0 < R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ∀ n ≤ k, ∀ x ∈ ball (0 : E) R, ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ n (fun y => a (r • y) i j) x‖ ≤ L := by
  classical
  let J := Fin (k + 1) × Fin 3 × Fin 3
  have hb : ∀ s : J, ∃ C : ℝ, ∀ x ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ s.1.val (fun y => a y s.2.1 s.2.2) x‖ ≤ C := by
    intro s
    exact (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
      ((ha s.2.1 s.2.2).continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hb
  let L := ∑ s : J, max 0 (C s)
  have hL : 0 ≤ L := Finset.sum_nonneg fun s _ => le_max_left _ _
  refine ⟨L, hL, ?_⟩
  intro r hr hr1 n hn x hx i j
  let s : J := (⟨n, Nat.lt_succ_of_le hn⟩, i, j)
  have hOrig : ‖iteratedFDeriv ℝ n (fun y => a y i j) (r • x)‖ ≤ L := by
    have hxR : ‖x‖ < R := by simpa using hx
    have hrx : r • x ∈ closedBall (0 : E) R := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      exact (mul_le_of_le_one_left (norm_nonneg x) hr1).trans hxR.le
    exact ((hC s (r • x) hrx).trans (le_max_right _ _)).trans
      (Finset.single_le_sum (fun t _ => le_max_left _ _) (Finset.mem_univ s))
  have hsmooth : ContDiff ℝ n (fun y => a y i j) :=
    (ha i j).of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_comp_const_smul r hsmooth, norm_smul, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg hr]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr hr1)).trans hOrig

/-- One radius and common finite coefficient jets construct actual smooth
elliptic bilinear forms for every rescaling of an identity-normalized field. -/
theorem exists_uniform_rescaled_bilinear_forms
    {a : E → Matrix (Fin 3) (Fin 3) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hsymm : ∀ x i j, a x i j = a x j i) (hzero : a 0 = 1)
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∃ B : SmoothEllipticBilinearForm 3 (ball (0 : E) R),
        B.a = (fun x => a (r • x)) ∧ B.lam = 1 / 2 ∧
        (∀ n ≤ k, ∀ x ∈ ball (0 : E) R, ∀ i j : Fin 3,
          ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) ∧
        ∀ x ∈ ball (0 : E) R, (∑ i : Fin 3, ∑ j : Fin 3,
          (B.a x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2) ≤ 1 / 4 := by
  obtain ⟨ρ, hρ, hρb⟩ := exists_coefficient_identity_radius
    (fun i j => (ha i j).continuous.continuousAt) hzero
  obtain ⟨L, hL, hLb⟩ := exists_common_rescaled_coefficient_jets ha k hR
  refine ⟨min 1 (ρ / R), lt_min (by norm_num) (div_pos hρ hR), L, hL, ?_⟩
  intro r hr hrδ
  have hr1 : r ≤ 1 := (hrδ.trans_le (min_le_left _ _)).le
  have hrR : r * R < ρ := (lt_div_iff₀ hR).mp (hrδ.trans_le (min_le_right _ _))
  have hnear (x : E) (hx : x ∈ ball (0 : E) R) :
      ∀ i j, |a (r • x) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 / 6 := by
    apply hρb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    have hxR : ‖x‖ < R := by simpa using hx
    exact (mul_le_mul_of_nonneg_left hxR.le hr).trans_lt hrR
  have hosc (x : E) (hx : x ∈ ball (0 : E) R) :
      (∑ i : Fin 3, ∑ j : Fin 3,
        (a (r • x) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2) ≤ 1 / 4 :=
    frobenius_le_quarter_of_entry_bound _ (hnear x hx)
  let B : SmoothEllipticBilinearForm 3 (ball (0 : E) R) :=
    { a := fun x => a (r • x)
      c := fun _ => 0
      symm := fun x i j => hsymm (r • x) i j
      smooth_a := fun i j => (ha i j).comp (contDiff_id.const_smul r)
      smooth_c := contDiff_const
      lam := 1 / 2
      capLam := 1 / 2
      hlam_pos := by norm_num
      hlam_le_capLam := le_rfl
      coercive := fun x hx v => coercive_of_frobenius_le_quarter _ (hosc x hx) v }
  exact ⟨B, rfl, rfl, hLb r hr hr1, hosc⟩

/-- The actual native density-inverse-metric field supplies the entire
uniform rescaled family; ellipticity and jet bounds are conclusions. -/
theorem exists_uniform_native_rescaled_bilinear_forms
    (g : RiemannianMetric 3 E) (hB : g.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0 = 1) (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∃ B : SmoothEllipticBilinearForm 3 (ball (0 : E) R),
        B.a = (fun x => nativeDivergenceMatrix g (r • x)) ∧ B.lam = 1 / 2 ∧
        (∀ n ≤ k, ∀ x ∈ ball (0 : E) R, ∀ i j : Fin 3,
          ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) ∧
        ∀ x ∈ ball (0 : E) R, (∑ i : Fin 3, ∑ j : Fin 3,
          (B.a x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2) ≤ 1 / 4 := by
  apply exists_uniform_rescaled_bilinear_forms
    (contDiff_nativeDivergenceMatrix g) ?_ (nativeDivergenceMatrix_zero g hB hρ) k hR
  intro x i j
  exact divergenceCoefficients_symm (g := g) (OpenPartialHomeomorph.refl E)
    contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn (by simp) i j

#print axioms coercive_of_frobenius_le_quarter
#print axioms exists_common_rescaled_coefficient_jets
#print axioms exists_uniform_rescaled_bilinear_forms
#print axioms exists_uniform_native_rescaled_bilinear_forms

end Yamabe3.Analysis.UniformElliptic
