import Yamabe3.Analysis.L2SquareNormBound

/-! Quantitative bounds survive the actual strong L2 construction. -/
noncomputable section
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis

theorem norm_tsum_sq_le_of_finite_square_energy
    {ι H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    {v : ι → H} {a : ι → ℝ} {C : ℝ}
    (ha : Summable a) (hC : 0 ≤ C)
    (hv : ∀ s : Finset ι, ‖∑ i ∈ s,v i‖^2 ≤ C*(∑ i ∈ s,a i)) :
    ‖∑' i,v i‖^2 ≤ C*(∑' i,a i) := by
  have hs : Tendsto (fun s : Finset ι => ∑ i ∈ s,v i) atTop (𝓝 (∑' i,v i)) :=
    (summable_of_finite_square_energy ha hC hv).hasSum
  have ht : Tendsto (fun s : Finset ι => ∑ i ∈ s,a i) atTop (𝓝 (∑' i,a i)) := ha.hasSum
  exact le_of_tendsto_of_tendsto (hs.norm.pow 2) (ht.const_mul C) (Eventually.of_forall hv)

theorem norm_L2_series_sq_le_of_finite_integrals
    {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℝ) (hf : ∀ i,MemLp (f i) 2 μ)
    {a : ι → ℝ} {C : ℝ} (ha : Summable a) (hC : 0 ≤ C)
    (hb : ∀ s : Finset ι,(∫ x,(∑ i ∈ s,f i x)^2 ∂μ) ≤ C*(∑ i ∈ s,a i)) :
    ‖∑' i,(hf i).toLp (f i)‖^2 ≤ C*(∑' i,a i) := by
  apply norm_tsum_sq_le_of_finite_square_energy ha hC
  intro s
  have hs := memLp_finsetSum s (fun i _ => hf i)
  rw [lp_finset_sum_toLp f hf s hs,UniformElliptic.native_norm_toLp_sq_eq_integral_sq]
  exact hb s

theorem norm_L2_series_sq_le_of_finite_eLpNorm_bound
    {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℝ) (hf : ∀ i,MemLp (f i) 2 μ)
    {a : ι → ℝ} {C : ℝ} (ha : Summable a) (ha0 : ∀ i,0 ≤ a i) (hC : 0 ≤ C)
    (hb : ∀ s : Finset ι,eLpNorm (fun x => ∑ i ∈ s,f i x) 2 μ ≤
      ENNReal.ofReal (Real.sqrt (C*(∑ i ∈ s,a i)))) :
    ‖∑' i,(hf i).toLp (f i)‖^2 ≤ C*(∑' i,a i) := by
  apply norm_tsum_sq_le_of_finite_square_energy ha hC
  intro s
  have hs := memLp_finsetSum s (fun i _ => hf i)
  rw [lp_finset_sum_toLp f hf s hs]
  exact norm_toLp_sq_le_of_eLpNorm_sqrt hs
    (mul_nonneg hC (Finset.sum_nonneg (fun i _ => ha0 i))) (hb s)

#print axioms norm_tsum_sq_le_of_finite_square_energy
#print axioms norm_L2_series_sq_le_of_finite_integrals
#print axioms norm_L2_series_sq_le_of_finite_eLpNorm_bound
end Yamabe3.Analysis
