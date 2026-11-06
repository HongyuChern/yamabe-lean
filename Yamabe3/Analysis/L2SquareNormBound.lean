import Yamabe3.Analysis.L2FiniteSquareSummability

/-! Conversion of actual eLpNorm square-root estimates into finite
Hilbert norm-square estimates. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Topology
namespace Yamabe3.Analysis

theorem norm_toLp_sq_le_of_eLpNorm_sqrt {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt B)) :
    ‖hf.toLp f‖^2 ≤ B := by
  rw [Lp.norm_toLp]
  have hn : (eLpNorm f 2 μ).toReal ≤ Real.sqrt B := by
    have ht := ENNReal.toReal_mono (by simp : ENNReal.ofReal (Real.sqrt B) ≠ ⊤) h
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg B)] using ht
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 μ),Real.sqrt_nonneg B,Real.sq_sqrt hB]

theorem summable_L2_of_finite_eLpNorm_bound
    {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℝ) (hf : ∀ i,MemLp (f i) 2 μ)
    {a : ι → ℝ} {C : ℝ} (ha : Summable a) (ha0 : ∀ i,0 ≤ a i) (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι,eLpNorm (fun x => ∑ i ∈ s,f i x) 2 μ ≤
      ENNReal.ofReal (Real.sqrt (C*(∑ i ∈ s,a i)))) :
    Summable (fun i => (hf i).toLp (f i)) := by
  apply summable_of_finite_square_energy ha hC
  intro s
  have hs := memLp_finsetSum s (fun i _ => hf i)
  rw [lp_finset_sum_toLp f hf s hs]
  exact norm_toLp_sq_le_of_eLpNorm_sqrt hs
    (mul_nonneg hC (Finset.sum_nonneg (fun i _ => ha0 i))) (hbound s)

#print axioms norm_toLp_sq_le_of_eLpNorm_sqrt
#print axioms summable_L2_of_finite_eLpNorm_bound
end Yamabe3.Analysis
