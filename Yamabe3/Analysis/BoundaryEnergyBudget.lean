import Yamabe3.Analysis.BoundaryUniformH2

/-! The actual square-integral budget is bounded by the finite L1 sum of
L2 norms. This converts the tangential estimate to a homogeneous bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev

/-- No integrability is assumed beyond the displayed actual L2 functions. -/
theorem sqrt_square_energy_le_l2_sum
    {α I : Type*} [MeasurableSpace α] [Fintype I] (μ : Measure α)
    (p : I → α → ℝ) (u f : α → ℝ)
    (hp : ∀ i, MemLp (p i) 2 μ) (hu : MemLp u 2 μ) (hf : MemLp f 2 μ) :
    Real.sqrt ((∫ x, ∑ i, p i x ^ 2 ∂μ) + (∫ x, u x ^ 2 ∂μ) + (∫ x, f x ^ 2 ∂μ)) ≤
      (∑ i, (eLpNorm (p i) 2 μ).toReal) + (eLpNorm u 2 μ).toReal + (eLpNorm f 2 μ).toReal := by
  have hp0 : 0 ≤ ∑ i, (eLpNorm (p i) 2 μ).toReal := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hu0 := (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm u 2 μ).toReal)
  have hf0 := (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm f 2 μ).toReal)
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (add_nonneg hp0 hu0) hf0, ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hp i).integrable_sq),
    ← eLpNorm_toReal_sq_eq_integral hu, ← eLpNorm_toReal_sq_eq_integral hf]
  simp_rw [← eLpNorm_toReal_sq_eq_integral (hp _)]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm (p i) 2 μ).toReal))
  nlinarith [mul_nonneg hp0 hu0, mul_nonneg hp0 hf0, mul_nonneg hu0 hf0]

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
open Poincare.Analysis.Sobolev.BoundaryTangential

theorem flatTangentialBudget_le_l2_sum
    (U : Set E) (C : Fin d → ℝ) (hC : ∀ k, 0 ≤ C k)
    (u f : E → ℝ) (p : Fin d → E → ℝ)
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (U ∩ halfSpace d)))
    (hu : MemLp u 2 (volume.restrict (U ∩ halfSpace d)))
    (hf : MemLp f 2 (volume.restrict (U ∩ halfSpace d))) :
    flatTangentialBudget U C u f p ≤ ENNReal.ofReal (∑ k, Real.sqrt (C k)) *
      ((∑ i, eLpNorm (p i) 2 (volume.restrict (U ∩ halfSpace d))) +
        eLpNorm u 2 (volume.restrict (U ∩ halfSpace d)) +
        eLpNorm f 2 (volume.restrict (U ∩ halfSpace d))) := by
  classical
  let μ := volume.restrict (U ∩ halfSpace d)
  let S : ℝ := (∑ i, (eLpNorm (p i) 2 μ).toReal) + (eLpNorm u 2 μ).toReal + (eLpNorm f 2 μ).toReal
  have hS : 0 ≤ S := add_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  have hSQ := sqrt_square_energy_le_l2_sum μ p u f hp hu hf
  have hE : ENNReal.ofReal S = (∑ i, eLpNorm (p i) 2 μ) + eLpNorm u 2 μ + eLpNorm f 2 μ := by
    dsimp only [S]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    simp only [μ, ENNReal.ofReal_toReal hu.eLpNorm_lt_top.ne,
      ENNReal.ofReal_toReal hf.eLpNorm_lt_top.ne, ENNReal.ofReal_toReal (hp _).eLpNorm_lt_top.ne]

  calc
    _ ≤ ∑ k, ENNReal.ofReal (Real.sqrt (C k) * S) := by
      apply Finset.sum_le_sum
      intro k _
      apply ENNReal.ofReal_le_ofReal
      rw [Real.sqrt_mul (hC k)]
      exact mul_le_mul_of_nonneg_left hSQ (Real.sqrt_nonneg _)
    _ = (∑ k, ENNReal.ofReal (Real.sqrt (C k))) * ENNReal.ofReal S := by
      simp only [ENNReal.ofReal_mul (Real.sqrt_nonneg _), Finset.sum_mul]
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.sqrt_nonneg (C k)), hE]

#print axioms sqrt_square_energy_le_l2_sum
#print axioms flatTangentialBudget_le_l2_sum
end Yamabe3.Analysis.UniformElliptic
