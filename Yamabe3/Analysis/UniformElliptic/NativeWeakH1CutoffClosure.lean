import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation
import PoincareLib.Analysis.Sobolev.Boundary.Approximation.Closure
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong compact cutoff closure for the actual weak H1 predicate

Bounded smooth cutoffs tending to one produce actual convergence of the
value and the original weak-gradient factor by dominated convergence.
The other product-rule term remains an explicit L2 error obligation.
Once that genuine error tends to zero, the actual product witnesses,
compact-support Sobolev approximation and its proved strong closure give
`MemH01` for the same function.

This general theorem does not by itself prove that the original forced
half-end satisfies its cutoff-error hypothesis. That production belongs
to the concrete boundary and tip estimates and the geometric cutoff family.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Weak

/-- The original scalar L2 function is recovered by bounded scalar
cutoffs tending to one almost everywhere. The products really belong
to L2 before their convergence is asserted. -/
theorem native_cutoff_mul_memLp_and_eLpNorm_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u : X → ℝ}
    (hu : MemLp u 2 μ) (χ : ℕ → X → ℝ)
    (hχ : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hrange : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1)) :
    (∀ n, MemLp (fun x => χ n x * u x) 2 μ) ∧
    Tendsto (fun n => eLpNorm (fun x => χ n x * u x - u x) 2 μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : MemLp (fun x => χ n x * u x) 2 μ := by
    apply MemLp.of_le_mul (g := u) (c := 1) hu ((hχ n).mul hu.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖χ n x * u x‖ ≤ 1 * ‖u x‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hrange n x).1, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hrange n x).2
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => (χ n x * u x - u x) ^ 2) μ :=
    ((hm n).sub hu).integrable_sq.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ,
      ‖(χ n x * u x - u x) ^ 2‖ ≤ u x ^ 2 := by
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hs : (χ n x - 1) ^ 2 ≤ 1 := by
        have hp := mul_nonneg (hrange n x).1 (sub_nonneg.mpr (hrange n x).2)
        nlinarith [(hrange n x).1, (hrange n x).2]
      calc
        _ = (χ n x - 1) ^ 2 * u x ^ 2 := by ring
        _ ≤ 1 * u x ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
        _ = _ := one_mul _
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => (χ n x * u x - u x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have hc : Tendsto (fun _ : ℕ => u x) atTop (𝓝 (u x)) := tendsto_const_nhds
    simpa using ((hx.mul hc).sub hc).pow 2
  have hint : Tendsto (fun n => ∫ x, (χ n x * u x - u x) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun x => u x ^ 2)
        hmeas hu.integrable_sq hbound hpoint)
  refine ⟨hm, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n x => χ n x * u x) hm u hu).mp
      (native_tendsto_toLp_of_integral_sq_sub hm hu hint)

/-- Actual smooth compact cutoffs and their true product-rule error
give zero-boundary Sobolev approximation of the same weak H1 function.
No zero trace or compact approximation is assumed for the input function. -/
theorem native_memH01_of_smooth_cutoffs
    {d : ℕ} [NeZero d] {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (w : MemW1pWitness 2 u O)
    (χ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n))
    (hc : ∀ n, HasCompactSupport (χ n))
    (hs : ∀ n, tsupport (χ n) ⊆ O)
    (hrange : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hlim : ∀ᵐ x ∂volume.restrict O,
      Tendsto (fun n => χ n x) atTop (𝓝 1))
    (herr : ∀ i : Fin d, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (χ n) x (EuclideanSpace.single i 1) * u x)
      2 (volume.restrict O)) atTop (𝓝 0)) :
    MemH01 u O := by
  classical
  have hex (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (χ n) x‖ ≤ C := by
    obtain ⟨A, hA⟩ := ((hc n).fderiv (𝕜 := ℝ)).isCompact.exists_bound_of_continuousOn
      ((hχ n).continuous_fderiv (by simp)).continuousOn
    refine ⟨max A 0, le_max_right _ _, ?_⟩
    intro x
    by_cases hx : x ∈ tsupport (fderiv ℝ (χ n))
    · exact (hA x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_right _ _
  choose C hC hCb using hex
  have habs (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (hrange n x).1]
    exact (hrange n x).2
  let uSeq : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x => χ n x * u x
  let wSeq (n : ℕ) : MemW1pWitness 2 (uSeq n) O :=
    w.mulSmoothBoundedP (by norm_num) hO (hχ n) zero_le_one (hC n) (habs n) (hCb n)
  have hseq (n : ℕ) : MemW01p 2 (uSeq n) O := by
    have hcompact : HasCompactSupport (uSeq n) := (hc n).mul_right
    have hsupport : tsupport (uSeq n) ⊆ O :=
      (tsupport_smul_subset_left (χ n) u).trans (hs n)
    simpa using memW01p_of_memW1p_of_tsupport_subset hO (p := 2) (by norm_num)
      (by simpa using (wSeq n).memW1p) hcompact hsupport
  have hχmeas (n : ℕ) : AEStronglyMeasurable (χ n) (volume.restrict O) :=
    (hχ n).continuous.aestronglyMeasurable
  have hv := (native_cutoff_mul_memLp_and_eLpNorm_tendsto w.memLp χ hχmeas hrange hlim).2
  apply MemW01p.of_tendsto_eLpNorm hO hseq wSeq w hv
  intro i
  have hg := native_cutoff_mul_memLp_and_eLpNorm_tendsto
    (w.weakGrad_component_memLp i) χ hχmeas hrange hlim
  have hbound (n : ℕ) :
      eLpNorm (fun x => (wSeq n).weakGrad x i - w.weakGrad x i) 2 (volume.restrict O) ≤
      eLpNorm (fun x => χ n x * w.weakGrad x i - w.weakGrad x i) 2 (volume.restrict O) +
      eLpNorm (fun x => fderiv ℝ (χ n) x (EuclideanSpace.single i 1) * u x)
        2 (volume.restrict O) := by
    have heq : (fun x => (wSeq n).weakGrad x i - w.weakGrad x i) =
        (fun x => (χ n x * w.weakGrad x i - w.weakGrad x i) +
          fderiv ℝ (χ n) x (EuclideanSpace.single i 1) * u x) := by
      funext x
      simp only [wSeq, MemW1pWitness.mulSmoothBoundedP, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    apply eLpNorm_add_le _ _ (by norm_num)
    · exact ((hg.1 n).sub (w.weakGrad_component_memLp i)).aestronglyMeasurable
    · exact (((hχ n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul
        w.memLp.aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hg.2.add (herr i)) (fun _ => bot_le) hbound

#print axioms native_cutoff_mul_memLp_and_eLpNorm_tendsto
#print axioms native_memH01_of_smooth_cutoffs

end Yamabe3.Analysis.UniformElliptic
