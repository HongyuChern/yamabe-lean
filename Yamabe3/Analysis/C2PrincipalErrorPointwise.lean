import Yamabe3.Analysis.NativePrincipalErrorRows

/-! Pointwise control of the genuine C2 representative, using its actual
first and second Frechet derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem norm_iteratedFDeriv_partial_finite_at {u : E → ℝ} {x : E} (j : ℕ)
    (hu : ContDiffAt ℝ (j+1) u x) (i : Fin 3) :
    ‖iteratedFDeriv ℝ j (partialDeriv i u) x‖ ≤ ‖iteratedFDeriv ℝ (j+1) u x‖ := by
  have hf : ContDiffAt ℝ j (fderiv ℝ u) x := hu.fderiv_right (by norm_cast)
  have hh := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ u)
    (c := EuclideanSpace.single i (1:ℝ)) (n := j) (x := x) hf le_rfl
  change ‖iteratedFDeriv ℝ j (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x‖ ≤ _
  simpa only [EuclideanSpace.norm_single,norm_one,one_mul,norm_iteratedFDeriv_fderiv] using hh

theorem norm_partial_le_first_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 1 u x) (i : Fin 3) :
    ‖partialDeriv i u x‖ ≤ ‖iteratedFDeriv ℝ 1 u x‖ := by
  simpa only [norm_iteratedFDeriv_zero] using norm_iteratedFDeriv_partial_finite_at 0 hu i

theorem norm_second_partial_le_second_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin 3) :
    ‖partialDeriv i (partialDeriv j u) x‖ ≤ ‖iteratedFDeriv ℝ 2 u x‖ := by
  have hp : ContDiffAt ℝ 1 (partialDeriv j u) x :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  exact (norm_partial_le_first_at hp i).trans (norm_iteratedFDeriv_partial_finite_at 1 hu j)

theorem nativePrincipalError_pointwise_bound (g : RiemannianMetric 3 E) (ε : ℝ)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {η M : ℝ} (hη : 0 ≤ η)
    (ha : ∀ i j, ‖nativeScaledPrincipalError g ε i j x‖ ≤ η)
    (hb : ∀ j, ‖nativeScaledFirstError g ε j x‖ ≤ η)
    (hU : ∀ j ≤ 2, ‖iteratedFDeriv ℝ j u x‖ ≤ M) :
    ‖nativePrincipalError g ε u x‖ ≤ 12*η*M := by
  rw [nativePrincipalError_eq_classical g ε hu]
  unfold nativeScaledGeometricError secondOrderPerturbation
  simp only [zero_mul,add_zero]
  have hsecond (i j) : ‖nativeScaledPrincipalError g ε i j x * partialDeriv i (partialDeriv j u) x‖ ≤ η*M := by
    rw [norm_mul]
    exact mul_le_mul (ha i j) ((norm_second_partial_le_second_at hu i j).trans (hU 2 le_rfl)) (norm_nonneg _) hη
  have hfirst (i) : ‖nativeScaledFirstError g ε i x * partialDeriv i u x‖ ≤ η*M := by
    rw [norm_mul]
    exact mul_le_mul (hb i) ((norm_partial_le_first_at (hu.of_le (by norm_num)) i).trans (hU 1 (by norm_num))) (norm_nonneg _) hη
  calc
    _ ≤ ‖∑ i : Fin 3, ∑ j : Fin 3, nativeScaledPrincipalError g ε i j x * partialDeriv i (partialDeriv j u) x‖ +
        ‖∑ i : Fin 3, nativeScaledFirstError g ε i x * partialDeriv i u x‖ := norm_add_le _ _
    _ ≤ (∑ i : Fin 3, ∑ j : Fin 3, η*M) + ∑ i : Fin 3, η*M := add_le_add
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hsecond i j)))))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hfirst i)))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat];ring

#print axioms norm_second_partial_le_second_at
#print axioms nativePrincipalError_pointwise_bound
end Yamabe3.Analysis.UniformElliptic
