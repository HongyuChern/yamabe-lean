import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support

/-! AE identities on a domain can be multiplied and extended to full
volume when the actual multiplier is supported in that domain. This
does not restrict a volume identity to a hypersurface. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
namespace Yamabe3.Analysis
theorem supported_mul_ae_of_restrict
    {X:Type*} [TopologicalSpace X] [MeasurableSpace X] {μ:Measure X}
    {O:Set X} (hO:MeasurableSet O) (χ:X→ℝ) (hs:tsupport χ⊆O)
    {u v:X→ℝ} (he:u=ᵐ[μ.restrict O]v) :
    (fun x=>χ x*u x)=ᵐ[μ]fun x=>χ x*v x := by
  have hi:O.indicator (fun x=>χ x*u x)=ᵐ[μ]O.indicator (fun x=>χ x*v x) :=
    (ae_eq_restrict_iff_indicator_ae_eq hO).mp ((EventuallyEq.refl _ _).mul he)
  filter_upwards [hi] with x hx
  by_cases hm:x∈O
  · simpa only [indicator_of_mem hm] using hx
  · rw [image_eq_zero_of_notMem_tsupport (fun h=>hm (hs h)),zero_mul,zero_mul]

#print axioms supported_mul_ae_of_restrict
end Yamabe3.Analysis
