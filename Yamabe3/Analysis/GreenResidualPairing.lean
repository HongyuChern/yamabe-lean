import Yamabe3.Analysis.Green.NativeLocalParametrix
import Yamabe3.Analysis.Green.NativeCutoffParametrix

/-!
# Genuine L2 domination and pairings for the regularized native residual

The actual residual is uniformly dominated by an explicitly constructed
native L2 function: the cutoff inverse radius plus two bounded annular
coefficients. This upgrades the earlier continuous-test limit to pairings
with arbitrary native L2 functions, including another singular Green function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open Yamabe3.RegularizedNewton
open Yamabe3.Parametrix

/-- The complete regularized residual is genuinely measurable for every
width, including the harmless totalized width zero. -/
theorem measurable_regularizedNativeResidual (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) : Measurable (regularizedNativeResidual g χ ε) := by
  have hρ := native_density_smooth_positive g
  have hD : ContDiff ℝ ∞ (fderiv ℝ (g.pullbackVolumeDensity id)) :=
    hρ.1.fderiv_right (by simp)
  have hp : Measurable (potential ε) := by
    unfold potential
    exact ((measurable_norm.pow_const 2).add measurable_const).pow_const _
  have hr : Measurable (fun x : E => (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) :=
    ((measurable_norm.pow_const 2).add measurable_const).pow_const _
  have hden : Measurable (regularizedDensityResidual (g.pullbackVolumeDensity id)
      (fun x => g.leviCivitaData.scalarCurvature x / 8) ε) :=
    (((hD.continuous.clm_apply continuous_id).measurable.div hρ.1.continuous.measurable).mul hr).add
      ((g.leviCivitaData.continuous_scalarCurvature.div_const 8).measurable.mul hp)
  have hcut : Measurable (cutoffError g χ ε) :=
    ((g.leviCivitaData.continuous_laplacian χ.contDiff.contMDiff).measurable.neg.mul hp).add
      ((continuous_cutoffGradientCoefficient g χ).measurable.mul hr)
  exact (χ.continuous.measurable.mul hden).add hcut

/-- Both parts of the explicit native residual converge pointwise away
from the pole. The pole itself will be discarded by its proved native nullity. -/
theorem tendsto_regularizedNativeResidual (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) {x : E} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => regularizedNativeResidual g χ ε x) (𝓝 0)
      (𝓝 (nativeResidual g χ x)) := by
  have hd := (tendsto_regularizedDensityResidual (ρ := g.pullbackVolumeDensity id)
    (V := fun y => g.leviCivitaData.scalarCurvature y / 8) hx).const_mul (χ x)
  have hL := (tendsto_potential hx).const_mul (-(g.leviCivitaData.laplacian χ x))
  have hB := (tendsto_radial_power hx 3).const_mul (cutoffGradientCoefficient g χ x)
  simpa only [regularizedNativeResidual, nativeResidual, cutoffError,
    singularCutoffError, Nat.cast_ofNat] using hd.add (hL.add hB)

/-- The native L2 dominating function is constructed from actual compact
bounds and actual cutoff derivatives. No domination field is assumed. -/
theorem exists_L2_dominator_regularizedNativeResidual (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) :
    ∃ H : E → ℝ, MemLp H 2 g.volumeMeasure ∧
      ∀ ε : ℝ, ∀ x : E, x ≠ 0 → ‖regularizedNativeResidual g χ ε x‖ ≤ H x := by
  let D := g.leviCivitaData
  let ρ := g.pullbackVolumeDensity id
  let V := fun x => D.scalarCurvature x / 8
  have hρ := native_density_smooth_positive g
  have hV : Continuous V := D.continuous_scalarCurvature.div_const 8
  obtain ⟨c, C, B, A, hc, hC, hb⟩ :=
    density_bounds_on_ball hρ.1 hρ.2 hzero hV χ.rOut_pos
  let H : E → ℝ := fun x =>
    (C / c + B) * (χ x * ‖x‖⁻¹) +
      (‖D.laplacian χ x‖ * χ.rIn⁻¹ +
        ‖cutoffGradientCoefficient g χ x‖ * (χ.rIn ^ 3)⁻¹)
  have hL2 : MemLp (fun x => D.laplacian χ x) 2 g.volumeMeasure :=
    (D.continuous_laplacian χ.contDiff.contMDiff).memLp_of_hasCompactSupport
      (D.hasCompactSupport_laplacian χ.hasCompactSupport)
  have hB2 : MemLp (cutoffGradientCoefficient g χ) 2 g.volumeMeasure :=
    (continuous_cutoffGradientCoefficient g χ).memLp_of_hasCompactSupport
      (hasCompactSupport_cutoffGradientCoefficient g χ)
  refine ⟨H, ((native_memLp_cutoff_inv_norm g χ).const_mul _).add
    ((hL2.norm.mul_const _).add (hB2.norm.mul_const _)), ?_⟩
  intro ε x hx
  have hDen : ‖χ x * regularizedDensityResidual ρ V ε x‖ ≤
      (C / c + B) * (χ x * ‖x‖⁻¹) := by
    by_cases hχx : χ x = 0
    · simp only [hχx, zero_mul, norm_zero, mul_zero, le_refl]
    · have hxball : x ∈ ball (0 : E) χ.rOut := by
        rw [← χ.support_eq]
        exact hχx
      have h := regularizedDensityResidual_bound ε hc hC (hb x hxball).1
        (hb x hxball).2.2.1 (hb x hxball).2.2.2 hx
      rw [norm_mul, Real.norm_of_nonneg χ.nonneg, Real.norm_eq_abs]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left h χ.nonneg
  have hL : ‖-(D.laplacian χ x) * potential ε x‖ ≤ ‖D.laplacian χ x‖ * χ.rIn⁻¹ := by
    have hz : ∀ y : E, ‖y‖ < χ.rIn → -(D.laplacian χ y) = 0 := by
      intro y hy
      rw [native_laplacian_bump_zero_inner g χ hy, neg_zero]
    simpa only [potential, Nat.cast_one, one_div, pow_one, norm_neg] using
      annular_coefficient_bound χ.rIn_pos hz ε 1 x
  have hB' : ‖cutoffGradientCoefficient g χ x *
      (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))‖ ≤
        ‖cutoffGradientCoefficient g χ x‖ * (χ.rIn ^ 3)⁻¹ := by
    simpa only [Nat.cast_ofNat] using annular_coefficient_bound χ.rIn_pos
      (fun y hy => cutoffGradientCoefficient_zero_inner g χ hy) ε 3 x
  calc
    _ ≤ ‖χ x * regularizedDensityResidual ρ V ε x‖ +
        (‖-(D.laplacian χ x) * potential ε x‖ +
          ‖cutoffGradientCoefficient g χ x * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ H x := add_le_add hDen (add_le_add hL hB')

/-- The actual regularized residual converges against every native L2
multiplier, by L2×L2 integrability and genuine dominated convergence. -/
theorem tendsto_integral_regularizedNativeResidual_L2 (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) {f : E → ℝ} (hf : MemLp f 2 g.volumeMeasure) :
    Tendsto (fun ε : ℝ => ∫ x, f x * regularizedNativeResidual g χ ε x ∂g.volumeMeasure)
      (𝓝 0) (𝓝 (∫ x, f x * nativeResidual g χ x ∂g.volumeMeasure)) := by
  obtain ⟨H, hH, hbound⟩ := exists_L2_dominator_regularizedNativeResidual g hzero χ
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass (by norm_num)
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ * H x)
  · exact Eventually.of_forall fun ε => hf.aestronglyMeasurable.mul
      (measurable_regularizedNativeResidual g χ ε).aestronglyMeasurable
  · exact Eventually.of_forall fun ε => by
      filter_upwards [g.volumeMeasure.ae_ne (0 : E)] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound ε x hx) (norm_nonneg _)
  · exact hf.norm.integrable_mul hH
  · filter_upwards [g.volumeMeasure.ae_ne (0 : E)] with x hx
    exact (tendsto_regularizedNativeResidual g χ hx).const_mul (f x)

#print axioms measurable_regularizedNativeResidual
#print axioms tendsto_regularizedNativeResidual
#print axioms exists_L2_dominator_regularizedNativeResidual
#print axioms tendsto_integral_regularizedNativeResidual_L2

end Yamabe3.Analysis.GreenParametrix
