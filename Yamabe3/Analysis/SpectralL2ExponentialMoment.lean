import Yamabe3.Analysis.SpectralL2ContinuousRepresentative

/-! Exact exponential moments of the weighted full-line kernel.
These retain the signed conjugation parameter and can be used to
bootstrap far-end bounds without replacing a weighted field by its
bounded unconjugated factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralMajorant_exp_identity (k δ a t s : ℝ) :
    spectralMajorant k δ (t-s)*Real.exp (a*s)=
      Real.exp (a*t)*spectralMajorant k (δ+a) (t-s) := by
  unfold spectralMajorant
  rw [div_mul_eq_mul_div,←mul_div_assoc]
  congr 1
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  ring

theorem spectralMajorant_exp_moment {k δ a : ℝ} (hk : 0<k) (ha : |δ+a|<k) (t : ℝ) :
    Integrable (fun s : ℝ => spectralMajorant k δ (t-s)*Real.exp (a*s)) ∧
    (∫s : ℝ,spectralMajorant k δ (t-s)*Real.exp (a*s))=
      Real.exp (a*t)/(k^2-(δ+a)^2) := by
  have he : (fun s : ℝ => spectralMajorant k δ (t-s)*Real.exp (a*s))=
      (fun s : ℝ => Real.exp (a*t)*spectralMajorant k (δ+a) (t-s)) :=
    funext (spectralMajorant_exp_identity k δ a t)
  rw [he]
  refine ⟨((spectralMajorant_integral hk ha).1.comp_sub_left t).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub_left_eq_self,(spectralMajorant_integral hk ha).2]
  ring

theorem spectralL2Convolution_exp_bound {ι : Type*} (k : ι→ℝ) {k₀ δ a C : ℝ}
    (hk₀ : 0<k₀) (hk : ∀i,k₀≤k i) (hδ : |δ|<k₀) (ha : |δ+a|<k₀)
    (F : ℝ→SpectralSpace ι) (hF : MemLp F 2)
    (hbound : ∀ᵐs : ℝ ∂volume,‖F s‖≤C*Real.exp (a*s)) (t : ℝ) :
    ‖spectralL2Convolution k hk₀ hk δ F t‖≤C*Real.exp (a*t)/(k₀^2-(δ+a)^2) := by
  have hi := ((spectralMajorant_exp_moment hk₀ ha t).1).const_mul C
  have hb : ∀ᵐs : ℝ ∂volume,‖weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖≤
      C*(spectralMajorant k₀ δ (t-s)*Real.exp (a*s)) := by
    filter_upwards [hbound] with s hs
    apply (((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))).trans
    exact (mul_le_mul_of_nonneg_left hs (spectralMajorant_nonneg hk₀ δ (t-s))).trans_eq (by ring)
  change ‖∫s : ℝ,weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖≤_
  apply (norm_integral_le_of_norm_le hi hb).trans_eq
  rw [integral_const_mul,(spectralMajorant_exp_moment hk₀ ha t).2]
  ring

#print axioms spectralMajorant_exp_identity
#print axioms spectralMajorant_exp_moment
#print axioms spectralL2Convolution_exp_bound
end Yamabe3.Analysis.Delaunay
