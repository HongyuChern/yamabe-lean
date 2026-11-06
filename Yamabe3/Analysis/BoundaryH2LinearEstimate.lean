import Yamabe3.Analysis.BoundaryEnergyBudget

/-! A homogeneous full Hessian estimate, with a finite constant fixed
before the source and solution. All norms refer to actual weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_flat_hessian_linear_estimate
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (u f : E → ℝ) (p : Fin d → E → ℝ),
      MemW01p 2 u (halfSpace d) →
      MemLp f 2 (volume.restrict (W ∩ halfSpace d)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d))) →
      (∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d)) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ W ∩ halfSpace d →
        (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j * p j x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W ∩ halfSpace d, f x * φ x) →
      MemWkp 2 2 u (V ∩ halfSpace d) ∧
      ∀ i j : Fin d,
        eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u (V ∩ halfSpace d))
          (V ∩ halfSpace d)) 2 (volume.restrict (V ∩ halfSpace d)) ≤ K *
          ((∑ k, eLpNorm (p k) 2 (volume.restrict (halfSpace d))) +
            eLpNorm u 2 (volume.restrict (halfSpace d)) + eLpNorm f 2 (volume.restrict (W ∩ halfSpace d))) := by
  classical
  obtain ⟨U, C, A, D, hU, hUc, hVU, hUW, hC, hA, hD, h⟩ :=
    exists_uniform_flat_H2_bound B hW hWc hV hVc hVW
  let T : ℝ≥0∞ := ENNReal.ofReal (∑ k, Real.sqrt (C k))
  let K : ℝ≥0∞ := T + ENNReal.ofReal B.lam⁻¹ *
    (1 + ENNReal.ofReal A * ((d : ℝ≥0∞) * d * T) + ENNReal.ofReal D * d)
  have hK : K ≠ ⊤ := by dsimp [K, T]; finiteness
  refine ⟨K, hK, ?_⟩
  intro u f p hu hf hp hw heq
  obtain ⟨hu2, hess⟩ := h u f p hu hf hp hw heq
  let N : ℝ≥0∞ := (∑ k, eLpNorm (p k) 2 (volume.restrict (halfSpace d))) +
    eLpNorm u 2 (volume.restrict (halfSpace d)) + eLpNorm f 2 (volume.restrict (W ∩ halfSpace d))
  have hUW' : U ∩ halfSpace d ⊆ W ∩ halfSpace d := inter_subset_inter_left _ hUW
  have hVW' : V ∩ halfSpace d ⊆ W ∩ halfSpace d := inter_subset_inter_left _ (subset_closure.trans hVW)
  have hbud : flatTangentialBudget U C u f p ≤ T * N := by
    apply (flatTangentialBudget_le_l2_sum U C hC u f p
      (fun i => (hp i).mono_measure (Measure.restrict_mono_set volume inter_subset_right))
      (hu.1.1.mono_measure (Measure.restrict_mono_set volume inter_subset_right))
      (hf.mono_measure (Measure.restrict_mono_set volume hUW'))).trans
    dsimp only [T, N]
    gcongr <;> exact inter_subset_right
  have hfN : eLpNorm f 2 (volume.restrict (V ∩ halfSpace d)) ≤ N :=
    (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVW')).trans (le_add_left le_rfl)
  have hpN : (∑ ij : Fin d × Fin d, eLpNorm (p ij.2) 2 (volume.restrict (V ∩ halfSpace d))) ≤
      (d : ℝ≥0∞) * N := by
    calc
      _ ≤ ∑ ij : Fin d × Fin d, eLpNorm (p ij.2) 2 (volume.restrict (halfSpace d)) := by
        apply Finset.sum_le_sum
        intro ij _
        exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume inter_subset_right)
      _ = (d : ℝ≥0∞) * ∑ k, eLpNorm (p k) 2 (volume.restrict (halfSpace d)) := by
        simp [Fintype.sum_prod_type]
      _ ≤ _ := by
        gcongr
        exact (le_add_right le_rfl).trans (le_add_right le_rfl)
  refine ⟨hu2, ?_⟩
  intro i j
  calc
    _ ≤ _ := hess i j
    _ ≤ T * N + ENNReal.ofReal B.lam⁻¹ *
        (N + ENNReal.ofReal A * ((d : ℝ≥0∞) * d * (T * N)) +
          ENNReal.ofReal D * ((d : ℝ≥0∞) * N)) := by gcongr
    _ = K * N := by dsimp only [K]; ring

#print axioms exists_flat_hessian_linear_estimate
end Yamabe3.Analysis.UniformElliptic
