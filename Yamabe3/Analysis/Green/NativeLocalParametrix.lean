import Yamabe3.Analysis.Green.NativeRegularization
import Yamabe3.Analysis.Green.RegularizedResidual
import Yamabe3.Analysis.Green.PotentialIntegralLimits
import Yamabe3.Analysis.Green.DensityBounds
import Yamabe3.Analysis.Green.NativeCutoffErrors
import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareLib.Geometry.Riemannian.Surface.Regularity

/-! Native-coordinate parametrix assembly. All measures and operators here
belong to an actual smooth Riemannian metric, and all residuals are explicit.
The normalized chart construction will provide the metric and its zero jet. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open Yamabe3.RegularizedNewton
open Yamabe3.Parametrix

theorem native_volume_eq_density (g : RiemannianMetric 3 E) :
    g.volumeMeasure = volume.withDensity
      (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) := by
  have h := g.map_restrict_volumeMeasure_symm (OpenPartialHomeomorph.refl E)
    contMDiffOn_id contMDiffOn_id
  simpa using h

theorem native_density_smooth_positive (g : RiemannianMetric 3 E) :
    ContDiff ℝ ∞ (g.pullbackVolumeDensity id) ∧
      ∀ x, 0 < g.pullbackVolumeDensity id x := by
  have h (x : E) := g.contDiffAt_pullbackVolumeDensity (f := id) (x := x)
    contMDiffAt_id (by simpa using Function.injective_id)
  exact ⟨contDiff_iff_contDiffAt.mpr (fun x => (h x).1), fun x => (h x).2⟩

theorem native_integral_eq_density (g : RiemannianMetric 3 E) (f : E → ℝ) :
    (∫ x, f x ∂g.volumeMeasure) = ∫ x, f x * g.pullbackVolumeDensity id x := by
  have hρ := native_density_smooth_positive g
  have hm : Measurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) :=
    ENNReal.continuous_ofReal.measurable.comp hρ.1.continuous.measurable
  rw [native_volume_eq_density, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_of_lt (hρ.2 _)), smul_eq_mul, mul_comm]

theorem native_memLp_cutoff_inv_norm (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) :
    MemLp (fun x : E => χ x * ‖x‖⁻¹) 2 g.volumeMeasure := by
  rw [native_volume_eq_density]
  exact memLp_cutoff_inv_norm_withDensity χ (native_density_smooth_positive g).1.continuous

theorem native_integrable_iff_density (g : RiemannianMetric 3 E) (f : E → ℝ) :
    Integrable f g.volumeMeasure ↔
      Integrable (fun x => f x * g.pullbackVolumeDensity id x) := by
  have hρ := native_density_smooth_positive g
  have hm : Measurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) :=
    ENNReal.continuous_ofReal.measurable.comp hρ.1.continuous.measurable
  rw [native_volume_eq_density,
    integrable_withDensity_iff hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_of_lt (hρ.2 _))]

def nativeResidual (g : RiemannianMetric 3 E) (χ : ContDiffBump (0 : E))
    (x : E) : ℝ :=
  χ x * densityResidual (g.pullbackVolumeDensity id)
    (fun y => g.leviCivitaData.scalarCurvature y / 8) x + singularCutoffError g χ x

def regularizedNativeResidual (g : RiemannianMetric 3 E) (χ : ContDiffBump (0 : E))
    (ε : ℝ) (x : E) : ℝ :=
  χ x * regularizedDensityResidual (g.pullbackVolumeDensity id)
    (fun y => g.leviCivitaData.scalarCurvature y / 8) ε x + cutoffError g χ ε x

/-- The complete exact native regularized source, before taking its limit. -/
theorem native_regularized_cutoff_source (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    (χ : ContDiffBump (0 : E)) {ε : ℝ} (hε : 0 < ε) (x : E) :
    -g.leviCivitaData.laplacian (fun y => χ y * potential ε y) x +
      (g.leviCivitaData.scalarCurvature x / 8) * (χ x * potential ε x) =
      χ x * kernel ε x + regularizedNativeResidual g χ ε x := by
  rw [native_conformalLaplacian_cutoff g χ hε,
    native_negative_laplacian_regularizedNewton g g.leviCivitaData hGauss hε]
  unfold regularizedNativeResidual regularizedDensityResidual
  ring

/-- Cutoff multiplication extends a local L2 function by zero, using actual
support and the bound 0 ≤ χ ≤ 1. It makes no global regularity assumption on f. -/
theorem memLp_cutoff_mul_of_local {μ : Measure E} (χ : ContDiffBump (0 : E))
    {R : ℝ} (hR : χ.rOut ≤ R) {f : E → ℝ}
    (hf : MemLp f 2 (μ.restrict (ball (0 : E) R))) :
    MemLp (fun x => χ x * f x) 2 μ := by
  have hi := (memLp_indicator_iff_restrict measurableSet_ball).mpr hf
  have hm : MemLp (fun x => χ x * (ball (0 : E) R).indicator f x) 2 μ := by
    apply hi.of_le (χ.continuous.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    exact Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs (χ x), abs_of_nonneg χ.nonneg]
      simpa using mul_le_mul_of_nonneg_right χ.le_one
        (norm_nonneg ((ball (0 : E) R).indicator f x)))
  apply hm.ae_eq
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ ball (0 : E) R
  · simp [hx]
  · have hχx : χ x = 0 := χ.zero_of_le_dist (hR.trans (not_lt.mp hx))
    simp [hx, hχx]

/-- The explicit full limiting residual belongs to native L2. The only
coordinate jet used here is the zero derivative supplied by the proved
normalized-coordinate construction. -/
theorem native_cutoffDensityResidual_memLp (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) :
    MemLp (fun x => χ x * densityResidual (g.pullbackVolumeDensity id)
      (fun y => g.leviCivitaData.scalarCurvature y / 8) x) 2 g.volumeMeasure := by
  let ρ := g.pullbackVolumeDensity id
  let V := fun x => g.leviCivitaData.scalarCurvature x / 8
  have hρ := native_density_smooth_positive g
  have hV : Continuous V := g.leviCivitaData.continuous_scalarCurvature.div_const 8
  obtain ⟨c, C, B, A, hc, hC, hb⟩ :=
    density_bounds_on_ball hρ.1 hρ.2 hzero hV χ.rOut_pos
  have hD : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.1.fderiv_right (by simp)
  have hm : Measurable (densityResidual ρ V) := by
    unfold densityResidual
    exact (((hD.continuous.clm_apply continuous_id).measurable.div
      (hρ.1.continuous.measurable.mul (measurable_norm.pow_const 3))).add
      (hV.measurable.div measurable_norm))
  have hlocal : MemLp (densityResidual ρ V) 2
      (g.volumeMeasure.restrict (ball (0 : E) χ.rOut)) := by
    rw [native_volume_eq_density, restrict_withDensity measurableSet_ball]
    apply memLp_withDensity_of_le_inv_norm (A := ENNReal.ofReal A) (C := C / c + B)
      ENNReal.ofReal_ne_top
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact ENNReal.ofReal_le_ofReal (hb x hx).2.1
    · exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx hx0
      exact densityResidual_bound hc hC (hb x hx).1 (hb x hx).2.2.1
        (hb x hx).2.2.2 hx0
  exact memLp_cutoff_mul_of_local χ le_rfl hlocal

theorem nativeResidual_memLp (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) : MemLp (nativeResidual g χ) 2 g.volumeMeasure :=
  (native_cutoffDensityResidual_memLp g hzero χ).add (memLp_singularCutoffError g χ)

#print axioms native_volume_eq_density
#print axioms native_density_smooth_positive
#print axioms native_integral_eq_density
#print axioms native_memLp_cutoff_inv_norm
#print axioms native_integrable_iff_density
#print axioms native_regularized_cutoff_source
#print axioms memLp_cutoff_mul_of_local
#print axioms nativeResidual_memLp

end Yamabe3.Analysis.GreenParametrix
