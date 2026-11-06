import Yamabe3.Analysis.BoundaryHessianEquation

/-! Quantitative recovery of the normal component from the actual strong
weak-Hessian equation. No source or solution dependent constant is chosen. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace Yamabe3.Analysis.UniformElliptic

/-- Algebraic normal recovery with the source sign inherited from divergence
form. The other components and lower-order terms remain explicit. -/
theorem normal_component_abs_bound
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (i₀ : I) (a q : I → ℝ) (b p : J → ℝ) (f lam C D : ℝ)
    (hlam : 0 < lam) (ha₀ : lam ≤ a i₀)
    (ha : ∀ i, i ≠ i₀ → |a i| ≤ C) (hb : ∀ j, |b j| ≤ D)
    (heq : (∑ i, a i * q i) + (∑ j, b j * p j) = -f) :
    |q i₀| ≤ lam⁻¹ * (|f| + C * (∑ i ∈ Finset.univ.erase i₀, |q i|) +
      D * ∑ j, |p j|) := by
  have hsplit := Finset.sum_erase_add Finset.univ (fun i => a i * q i)
    (Finset.mem_univ i₀)
  have hid : a i₀ * q i₀ = -f - (∑ i ∈ Finset.univ.erase i₀, a i * q i) -
      ∑ j, b j * p j := by linarith
  have hbnd : |a i₀ * q i₀| ≤ |f| + C * (∑ i ∈ Finset.univ.erase i₀, |q i|) +
      D * ∑ j, |p j| := by
    rw [hid]
    calc
      _ ≤ |f| + |∑ i ∈ Finset.univ.erase i₀, a i * q i| + |∑ j, b j * p j| := by
        calc
          _ ≤ |-f - ∑ i ∈ Finset.univ.erase i₀, a i * q i| + |∑ j, b j * p j| := abs_sub _ _
          _ ≤ _ := by gcongr; simpa using abs_sub (-f) (∑ i ∈ Finset.univ.erase i₀, a i * q i)
      _ ≤ |f| + (∑ i ∈ Finset.univ.erase i₀, |a i * q i|) + ∑ j, |b j * p j| := by
        gcongr <;> apply Finset.abs_sum_le_sum_abs
      _ ≤ |f| + (∑ i ∈ Finset.univ.erase i₀, C * |q i|) + ∑ j, D * |p j| := by
        gcongr with i hi
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (ha i (Finset.mem_erase.mp hi).1) (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)
      _ = _ := by simp only [Finset.mul_sum]
  have hbound : lam * |q i₀| ≤ |f| + C * (∑ i ∈ Finset.univ.erase i₀, |q i|) + D * ∑ j, |p j| :=
    (mul_le_mul_of_nonneg_right ha₀ (abs_nonneg (q i₀))).trans (by
      simpa only [abs_mul, abs_of_pos (hlam.trans_le ha₀)] using hbnd)
  rw [mul_comm lam⁻¹, ← div_eq_mul_inv]
  exact (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hbound)

/-- An actual a.e. equation yields an L² norm estimate. In particular this
does not infer boundary values by restricting a volume-a.e. identity. -/
theorem normal_component_eLpNorm_bound
    {α I J : Type*} [MeasurableSpace α] [Fintype I] [DecidableEq I] [Fintype J]
    (μ : Measure α) (i₀ : I) (a q : I → α → ℝ) (b p : J → α → ℝ) (f : α → ℝ)
    (lam C D : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha₀ : ∀ᵐ x ∂μ, lam ≤ a i₀ x)
    (ha : ∀ᵐ x ∂μ, ∀ i, i ≠ i₀ → |a i x| ≤ C)
    (hb : ∀ᵐ x ∂μ, ∀ j, |b j x| ≤ D)
    (heq : ∀ᵐ x ∂μ, (∑ i, a i x * q i x) + (∑ j, b j x * p j x) = -f x)
    (hf : AEStronglyMeasurable f μ) (hq : ∀ i, AEStronglyMeasurable (q i) μ)
    (hp : ∀ j, AEStronglyMeasurable (p j) μ) :
    eLpNorm (q i₀) 2 μ ≤ ENNReal.ofReal lam⁻¹ *
      (eLpNorm f 2 μ + ENNReal.ofReal C * (∑ i ∈ Finset.univ.erase i₀, eLpNorm (q i) 2 μ) +
        ENNReal.ofReal D * ∑ j, eLpNorm (p j) 2 μ) := by
  classical
  let Q : α → ℝ := ∑ i ∈ Finset.univ.erase i₀, fun x => ‖q i x‖
  let P : α → ℝ := ∑ j, fun x => ‖p j x‖
  have hQ : AEStronglyMeasurable Q μ := Finset.aestronglyMeasurable_sum _ (fun i _ => (hq i).norm)
  have hP : AEStronglyMeasurable P μ := Finset.aestronglyMeasurable_sum _ (fun j _ => (hp j).norm)
  have hsumQ : eLpNorm Q 2 μ ≤ ∑ i ∈ Finset.univ.erase i₀, eLpNorm (q i) 2 μ := by
    simpa only [Q, Finset.sum_apply, eLpNorm_norm] using
      (eLpNorm_sum_le (fun i (_ : i ∈ Finset.univ.erase i₀) => (hq i).norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hsumP : eLpNorm P 2 μ ≤ ∑ j, eLpNorm (p j) 2 μ := by
    simpa only [P, Finset.sum_apply, eLpNorm_norm] using
      (eLpNorm_sum_le (fun j (_ : j ∈ Finset.univ) => (hp j).norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hscale (c : ℝ) (hc : 0 ≤ c) (v : α → ℝ) :
      eLpNorm (c • v) 2 μ = ENNReal.ofReal c * eLpNorm v 2 μ := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  calc
    _ ≤ eLpNorm (lam⁻¹ • ((fun x => ‖f x‖) + C • Q + D • P)) 2 μ := by
      apply eLpNorm_mono_ae_real
      filter_upwards [ha₀, ha, hb, heq] with x hx₀ hx hx' he
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.norm_eq_abs, Q, P, Finset.sum_apply] using
        normal_component_abs_bound i₀ (fun i => a i x) (fun i => q i x)
          (fun j => b j x) (fun j => p j x) (f x) lam C D hlam hx₀ hx hx' he
    _ = ENNReal.ofReal lam⁻¹ * eLpNorm ((fun x => ‖f x‖) + C • Q + D • P) 2 μ :=
      hscale _ (inv_nonneg.mpr hlam.le) _
    _ ≤ ENNReal.ofReal lam⁻¹ *
        (eLpNorm ((fun x => ‖f x‖) + C • Q) 2 μ + eLpNorm (D • P) 2 μ) := by
      gcongr
      exact eLpNorm_add_le (hf.norm.add (hQ.const_smul C)) (hP.const_smul D) (by norm_num)
    _ ≤ ENNReal.ofReal lam⁻¹ *
        (eLpNorm (fun x => ‖f x‖) 2 μ + eLpNorm (C • Q) 2 μ + eLpNorm (D • P) 2 μ) := by
      gcongr
      exact eLpNorm_add_le hf.norm (hQ.const_smul C) (by norm_num)
    _ = ENNReal.ofReal lam⁻¹ *
        (eLpNorm f 2 μ + ENNReal.ofReal C * eLpNorm Q 2 μ + ENNReal.ofReal D * eLpNorm P 2 μ) := by
      rw [eLpNorm_norm, hscale C hC, hscale D hD]
    _ ≤ _ := by gcongr

#print axioms normal_component_abs_bound
#print axioms normal_component_eLpNorm_bound
end Yamabe3.Analysis.UniformElliptic
