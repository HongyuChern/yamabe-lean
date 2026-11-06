import Yamabe3.Analysis.SpectralL2WeakEquation
import Yamabe3.Analysis.UniformElliptic.NativeL2SquareConvergence

/-! The actual entrance coordinate gains precisely three halves of a
spectral order from an L2 source. The estimate is computed from the same
Green integral, not postulated as a trace regularity hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay

theorem integral_mul_sq_le_integral_sq_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,f x*g x ∂μ)^2 ≤ (∫ x,f x^2 ∂μ)*(∫ x,g x^2 ∂μ) := by
  have he : (∫ x,f x*g x ∂μ)=inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,Real.inner_apply,mul_comm]
  rw [he,←UniformElliptic.native_norm_toLp_sq_eq_integral_sq hf,
    ←UniformElliptic.native_norm_toLp_sq_eq_integral_sq hg,←mul_pow]
  have h := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2

theorem spectralMajorant_square_integral {k δ : ℝ} (hk : 0<k) (hδ : |δ|<k) :
    (∫ t : ℝ,spectralMajorant k δ t^2)=1/(4*k*(k^2-δ^2)) := by
  have h2 : |2*δ|<2*k := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)];linarith
  have he : (fun t => spectralMajorant k δ t^2)=fun t => spectralMajorant (2*k) (2*δ) t/k := by
    funext t
    unfold spectralMajorant
    rw [div_pow,←Real.exp_nat_mul]
    have hex : (2:ℝ)*(-δ*t-k*|t|)=-(2*δ)*t-(2*k)*|t| := by ring
    simp only [Nat.cast_ofNat,hex]
    field_simp <;> ring
  rw [he,integral_div,(spectralMajorant_integral (by linarith) h2).2]
  rw [show (2*k)^2-(2*δ)^2=4*(k^2-δ^2) by ring]
  field_simp

theorem spectralL2Convolution_coordinate_integral {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) (i : ι) :
    spectralL2Convolution k hk₀ hk δ F t i =
      -(∫ s : ℝ,spectralMajorant (k i) δ (t-s)*F s i) := by
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  change ev (∫ s : ℝ,weightedSpectralKernel k hk₀ hk δ (t-s) (F s))=_
  rw [←ev.integral_comp_comm (spectralL2Convolution_everywhere_integrable k hk₀ hk hδ F hF t),←integral_neg]
  have hscalar (a b : ℝ) : Real.exp (-δ*a)*(scalarGreenKernel (k i) a*b)=
      -(spectralMajorant (k i) δ a*b) := by
    unfold scalarGreenKernel spectralMajorant
    rw [show Real.exp (-δ*a-k i*|a|)=Real.exp (-δ*a)*Real.exp (-k i*|a|) by
      simp only [sub_eq_add_neg,Real.exp_add,neg_mul]]
    ring
  exact integral_congr_ae (Eventually.of_forall fun s => hscalar (t-s) (F s i))

theorem spectralL2Convolution_coordinate_square_bound {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀)
    (F : ℝ → SpectralSpace ι) (hF : MemLp F 2) (t : ℝ) (i : ι) :
    (spectralL2Convolution k hk₀ hk δ F t i)^2 ≤
      (1/(4*k i*(k i^2-δ^2)))*(∫ s : ℝ,(F s i)^2) := by
  have hki := hk₀.trans_le (hk i)
  have hδi := hδ.trans_le (hk i)
  have hFi := (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).comp_memLp' hF
  have h := integral_mul_sq_le_integral_sq_mul volume (spectralMajorant_translate_memLp hki hδi t) hFi
  rw [spectralL2Convolution_coordinate_integral k hk₀ hk hδ F hF t i,neg_sq]
  have he : (∫ s : ℝ,spectralMajorant (k i) δ (t-s)^2)=1/(4*k i*(k i^2-δ^2)) := by
    rw [integral_sub_left_eq_self (fun s : ℝ => spectralMajorant (k i) δ s^2) volume t]
    exact spectralMajorant_square_integral hki hδi
  rw [he] at h
  exact h

#print axioms integral_mul_sq_le_integral_sq_mul
#print axioms spectralMajorant_square_integral
#print axioms spectralL2Convolution_coordinate_integral
#print axioms spectralL2Convolution_coordinate_square_bound
end Yamabe3.Analysis.Delaunay
