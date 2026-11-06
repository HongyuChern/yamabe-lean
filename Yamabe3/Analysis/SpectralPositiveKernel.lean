import Yamabe3.Analysis.PositiveKernelResolvent
import Yamabe3.Analysis.SpectralKernelReflection
import Yamabe3.Analysis.SpectralIntegralPotentialInverse
import Mathlib.MeasureTheory.Group.LIntegral

/-! The actual weight-conjugated exponential majorant as a positive
kernel. Potential-weighted row integrals retain the original convolution
and the exact denominator k^2-delta^2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralPositiveKernel (k δ x y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (spectralMajorant k δ (x-y))
def spectralPotentialMeasure (V : ℝ →ᵇ ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal |V y|)

theorem spectralPositiveKernel_measurable (k δ : ℝ) :
    Measurable (Function.uncurry (spectralPositiveKernel k δ)) := by
  unfold spectralPositiveKernel spectralMajorant Function.uncurry
  fun_prop

theorem spectralPositiveKernel_flip (k δ : ℝ) :
    Function.swap (spectralPositiveKernel k δ)=spectralPositiveKernel k (-δ) := by
  funext x y
  change ENNReal.ofReal (spectralMajorant k δ (y-x))=ENNReal.ofReal (spectralMajorant k (-δ) (x-y))
  congr 1
  rw [show y-x=-(x-y) by ring]
  simpa only [neg_neg] using spectralMajorant_reverse k (-δ) (x-y)

theorem spectralPositiveKernel_row_mass {k δ : ℝ} (hk : 0<k) (hδ : |δ|<k) (x : ℝ) :
    (∫⁻ y,spectralPositiveKernel k δ x y)=ENNReal.ofReal (1/(k^2-δ^2)) := by
  unfold spectralPositiveKernel
  rw [lintegral_sub_left_eq_self (fun s => ENNReal.ofReal (spectralMajorant k δ s)) x]
  rw [← ofReal_integral_eq_lintegral_ofReal (spectralMajorant_integral hk hδ).1
    (Eventually.of_forall (spectralMajorant_nonneg hk δ)),(spectralMajorant_integral hk hδ).2]

theorem spectralPositiveKernel_potential_row {k δ : ℝ} (hk : 0<k) (hδ : |δ|<k)
    (V : ℝ →ᵇ ℝ) (x : ℝ) :
    (∫⁻ y,spectralPositiveKernel k δ x y ∂spectralPotentialMeasure V)=
      ENNReal.ofReal (∫ s : ℝ,spectralMajorant k δ s * |V (x-s)|) := by
  have hmV : Measurable (fun y => ENNReal.ofReal |V y|) := V.continuous.abs.measurable.ennreal_ofReal
  have hmK : Measurable (spectralPositiveKernel k δ x) :=
    (spectralPositiveKernel_measurable k δ).comp (measurable_const.prodMk measurable_id)
  unfold spectralPotentialMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume hmV hmK]
  change (∫⁻ y,ENNReal.ofReal |V y| *ENNReal.ofReal (spectralMajorant k δ (x-y)))=_
  calc
    _ = ∫⁻ y,ENNReal.ofReal (spectralMajorant k δ (x-y) * |V y|) := by
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul (spectralMajorant_nonneg hk δ (x-y)),mul_comm]
    _ = ∫⁻ s,ENNReal.ofReal (spectralMajorant k δ s * |V (x-s)|) := by
      have hh := lintegral_sub_left_eq_self (μ := volume) (fun s : ℝ => ENNReal.ofReal (spectralMajorant k δ s * |V (x-s)|)) x
      simpa only [sub_sub_cancel] using hh
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (spectralMajorant_potential_integrable hk hδ V x)
      (Eventually.of_forall (fun s => mul_nonneg (spectralMajorant_nonneg hk δ s) (abs_nonneg _)))).symm

#print axioms spectralPositiveKernel_row_mass
#print axioms spectralPositiveKernel_potential_row
#print axioms spectralPositiveKernel_flip
end Yamabe3.Analysis.Delaunay
