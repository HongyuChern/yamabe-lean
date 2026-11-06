import Yamabe3.Analysis.BoundaryH2LinearEstimate
import Yamabe3.Analysis.BoundarySobolevMultiplier

/-! The full actual H2 norm is controlled by the original H1 zero-boundary
solution and L2 source. No second derivative is an input to the estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
/-- The genuine norm includes both the value and every lower weak derivative. -/
theorem wkpNorm_two_eq_one_add_hessian (u : E → ℝ) (O : Set E) :
    iteratedWeakSobolevNorm 2 2 u O = iteratedWeakSobolevNorm 1 2 u O +
      ∑ j : Fin d, ∑ i : Fin d,
        eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O) 2 (volume.restrict O) := by
  rw [wkpNorm_succ_eq 1]
  simp_rw [wkpNorm_succ_eq 0, wkpNorm_zero, Finset.sum_add_distrib]
  rw [add_assoc]

/-- A fixed domain pair and elliptic form determine a finite operator bound
before choosing the solution/source. This is full H2, not just a seminorm. -/
theorem exists_flat_H2_sobolev_estimate
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemW01p 2 u (halfSpace d) → MemLp f 2 (volume.restrict (W ∩ halfSpace d)) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ halfSpace d →
        (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j *
          chosenWeakPartial' 2 j u (halfSpace d) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          ∫ x in W ∩ halfSpace d, f x * φ x) →
      MemWkp 2 2 u (V ∩ halfSpace d) ∧
      iteratedWeakSobolevNorm 2 2 u (V ∩ halfSpace d) ≤ K *
        (iteratedWeakSobolevNorm 1 2 u (halfSpace d) + eLpNorm f 2 (volume.restrict (W ∩ halfSpace d))) := by
  classical
  obtain ⟨K, hK, h⟩ := exists_flat_hessian_linear_estimate B hW hWc hV hVc hVW
  refine ⟨1 + (d : ℝ≥0∞) * d * K, by finiteness, ?_⟩
  intro u f hu hf heq
  have hh := h u f (fun i => chosenWeakPartial' 2 i u (halfSpace d)) hu hf
    (fun i => chosenWeakPartial'_memLp_of_mem hu.1 i)
    (fun i => chosenWeakPartial'_isWeakPartial_of_mem hu.1 i) heq
  have h1 : MemWkp 1 2 u (halfSpace d) := (MemWkp.one_iff_memW1p).mpr hu.1
  have hlow : iteratedWeakSobolevNorm 1 2 u (V ∩ halfSpace d) ≤
      iteratedWeakSobolevNorm 1 2 u (halfSpace d) :=
    wkpNorm_mono_set (by norm_num) (hV.inter isOpen_halfSpace) inter_subset_right h1
  have hnorm : (∑ k, eLpNorm (chosenWeakPartial' 2 k u (halfSpace d)) 2 (volume.restrict (halfSpace d))) +
      eLpNorm u 2 (volume.restrict (halfSpace d)) = iteratedWeakSobolevNorm 1 2 u (halfSpace d) := by
    rw [wkpNorm_succ_eq 0]
    simp_rw [wkpNorm_zero]
    exact add_comm _ _
  refine ⟨hh.1, ?_⟩
  rw [wkpNorm_two_eq_one_add_hessian]
  calc
    _ ≤ iteratedWeakSobolevNorm 1 2 u (halfSpace d) + ∑ _j : Fin d, ∑ _i : Fin d,
        K * (iteratedWeakSobolevNorm 1 2 u (halfSpace d) + eLpNorm f 2 (volume.restrict (W ∩ halfSpace d))) := by
      apply add_le_add hlow
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      simpa only [hnorm] using hh.2 i j
    _ ≤ (iteratedWeakSobolevNorm 1 2 u (halfSpace d) + eLpNorm f 2 (volume.restrict (W ∩ halfSpace d))) +
        ∑ _j : Fin d, ∑ _i : Fin d, K *
          (iteratedWeakSobolevNorm 1 2 u (halfSpace d) + eLpNorm f 2 (volume.restrict (W ∩ halfSpace d))) :=
      add_le_add (le_add_right le_rfl) le_rfl
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

#print axioms wkpNorm_two_eq_one_add_hessian
#print axioms exists_flat_H2_sobolev_estimate
end Yamabe3.Analysis.UniformElliptic
