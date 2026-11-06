import Yamabe3.Analysis.UniformElliptic.NativeC1StrongLimit

/-! Two L2 limits agree when the actual approximants approach each other.
The conclusion is a.e. equality for the same measure, not a restriction
to a measure-zero boundary. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic

theorem native_ae_eq_of_approaching_L2_approximants
    {ι X : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι} [NeBot l]
    {f g : ι → X → ℝ} {U V : X → ℝ}
    (hf : ∀ a,MemLp (f a) 2 μ) (hg : ∀ a,MemLp (g a) 2 μ)
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hfu : Tendsto (fun a => ∫ x,(f a x-U x)^2 ∂μ) l (𝓝 0))
    (hgv : Tendsto (fun a => ∫ x,(g a x-V x)^2 ∂μ) l (𝓝 0))
    (hfg : Tendsto (fun a => ∫ x,(f a x-g a x)^2 ∂μ) l (𝓝 0)) :
    U =ᵐ[μ] V := by
  have hu := native_tendsto_toLp_of_integral_sq_sub_filter hf hU hfu
  have hv := native_tendsto_toLp_of_integral_sq_sub_filter hg hV hgv
  have ht := (hu.sub hv).norm.pow 2
  have hz : Tendsto (fun a => ‖(hf a).toLp (f a)-(hg a).toLp (g a)‖^2) l (𝓝 0) := by
    simpa only [native_norm_toLp_sub_sq_eq_integral_sq] using hfg
  have he : ‖hU.toLp U-hV.toLp V‖^2=0 := tendsto_nhds_unique ht hz
  have hn : ‖hU.toLp U-hV.toLp V‖=0 := by nlinarith [norm_nonneg (hU.toLp U-hV.toLp V)]
  have heq : hU.toLp U=hV.toLp V := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hc : (hU.toLp U : X → ℝ) =ᵐ[μ] (hV.toLp V : X → ℝ) := by rw [heq]
  exact hU.coeFn_toLp.symm.trans (hc.trans hV.coeFn_toLp)

#print axioms native_ae_eq_of_approaching_L2_approximants
end Yamabe3.Analysis.UniformElliptic
