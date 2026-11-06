import Yamabe3.Analysis.SquareEnergySummability
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! A finite square-integral bound constructs one L2 limit of the actual
finite sums. It does not assume a pointwise infinite representative. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis

theorem lp_finset_sum_coe_ae {ι X : Type*} [MeasurableSpace X]
    {μ : Measure X} (v : ι → Lp ℝ 2 μ) (s : Finset ι) :
    (⇑(∑ i ∈ s,v i)) =ᵐ[μ] (fun x => ∑ i ∈ s,v i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    exact hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (v i) (∑ j ∈ s,v j),ih] with x hx hy
    simpa only [Pi.add_apply,hy] using hx

theorem lp_finset_sum_toLp {ι X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : ι → X → ℝ) (hf : ∀ i,MemLp (f i) 2 μ)
    (s : Finset ι) (hs : MemLp (fun x => ∑ i ∈ s,f i x) 2 μ) :
    (∑ i ∈ s,(hf i).toLp (f i)) = hs.toLp (fun x => ∑ i ∈ s,f i x) := by
  apply Lp.ext
  have hterms : ∀ᵐ x ∂μ,∀ i ∈ s,((hf i).toLp (f i) : X → ℝ) x=f i x := by
    exact (Finset.eventually_all s).mpr (fun i _ => (hf i).coeFn_toLp)
  filter_upwards [lp_finset_sum_coe_ae (fun i => (hf i).toLp (f i)) s,
    hterms,hs.coeFn_toLp] with x hx ht hsx
  rw [hx,hsx]
  exact Finset.sum_congr rfl (fun i hi => ht i hi)

theorem exists_L2_sum_of_finite_square_integrals
    {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ι → X → ℝ) (hf : ∀ i,MemLp (f i) 2 μ)
    {a : ι → ℝ} {C : ℝ} (ha : Summable a) (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι,(∫ x,(∑ i ∈ s,f i x)^2 ∂μ) ≤ C*(∑ i ∈ s,a i)) :
    ∃ U : Lp ℝ 2 μ, Tendsto
      (fun s : Finset ι => ∑ i ∈ s,(hf i).toLp (f i)) atTop (𝓝 U) := by
  have hsum (s : Finset ι) : MemLp (fun x => ∑ i ∈ s,f i x) 2 μ :=
    memLp_finsetSum _ (fun i _ => hf i)
  have hb (s : Finset ι) : ‖∑ i ∈ s,(hf i).toLp (f i)‖^2 ≤ C*(∑ i ∈ s,a i) := by
    rw [lp_finset_sum_toLp f hf s (hsum s),UniformElliptic.native_norm_toLp_sq_eq_integral_sq]
    exact hbound s
  exact ⟨_,(summable_of_finite_square_energy ha hC hb).hasSum⟩

#print axioms lp_finset_sum_toLp
#print axioms exists_L2_sum_of_finite_square_integrals
end Yamabe3.Analysis
