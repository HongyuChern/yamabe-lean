import Yamabe3.Analysis.Green.NativeLocalParametrix
import Yamabe3.Analysis.Green.NativeCutoffL2Limits
import Yamabe3.Analysis.GreenClassical

/-! The point-source test identity for the actual Gauss-coordinate metric.
This module takes the singular limit of proved native smooth identities.
It does not place a Dirac measure in the H1 dual. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.RegularizedNewton
open Yamabe3.Parametrix

private theorem continuous_regularizedDensityResidual (g : RiemannianMetric 3 E)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedDensityResidual (g.pullbackVolumeDensity id)
      (fun x => g.leviCivitaData.scalarCurvature x / 8) ε) := by
  have hρ := native_density_smooth_positive g
  have hD : ContDiff ℝ ∞ (fderiv ℝ (g.pullbackVolumeDensity id)) :=
    hρ.1.fderiv_right (by simp)
  have hp : Continuous (fun x : E => (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) :=
    (((contDiff_id.norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun x => (normSq_add_sq_pos hε x).ne') : ContDiff ℝ ∞ _).continuous
  exact (((hD.continuous.clm_apply continuous_id).div hρ.1.continuous
    (fun x => (hρ.2 x).ne')).mul hp).add
    ((g.leviCivitaData.continuous_scalarCurvature.div_const 8).mul
      (contDiff_potential hε).continuous)

private theorem continuous_cutoffError (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (cutoffError g χ ε) := by
  have hp : Continuous (fun x : E => (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) :=
    (((contDiff_id.norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun x => (normSq_add_sq_pos hε x).ne') : ContDiff ℝ ∞ _).continuous
  exact ((g.leviCivitaData.continuous_laplacian χ.contDiff.contMDiff).neg.mul
    (contDiff_potential hε).continuous).add
      ((continuous_cutoffGradientCoefficient g χ).mul hp)

private theorem compact_cutoffError (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) : HasCompactSupport (cutoffError g χ ε) :=
  (g.leviCivitaData.hasCompactSupport_laplacian χ.hasCompactSupport).neg.mul_right.add
    (hasCompactSupport_cutoffGradientCoefficient g χ).mul_right

/-- The whole-space residual integral limit follows from the local bound
on the ball supporting the actual cutoff. -/
theorem tendsto_integral_cutoff_densityResidual (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) {φ : E → ℝ} (hφ : Continuous φ) :
    Tendsto (fun ε : ℝ => ∫ x : E,
      (φ x * χ x * g.pullbackVolumeDensity id x) *
        regularizedDensityResidual (g.pullbackVolumeDensity id)
          (fun y => g.leviCivitaData.scalarCurvature y / 8) ε x) (𝓝 0)
      (𝓝 (∫ x : E, (φ x * χ x * g.pullbackVolumeDensity id x) *
        densityResidual (g.pullbackVolumeDensity id)
          (fun y => g.leviCivitaData.scalarCurvature y / 8) x)) := by
  let ρ := g.pullbackVolumeDensity id
  let V := fun x => g.leviCivitaData.scalarCurvature x / 8
  let ψ := fun x => φ x * χ x * ρ x
  have hρ := native_density_smooth_positive g
  have hV : Continuous V := g.leviCivitaData.continuous_scalarCurvature.div_const 8
  obtain ⟨c, C, B, A, hc, hC, hb⟩ :=
    density_bounds_on_ball hρ.1 hρ.2 hzero hV χ.rOut_pos
  have hψ : Continuous ψ := (hφ.mul χ.continuous).mul hρ.1.continuous
  have hψc : HasCompactSupport ψ := χ.hasCompactSupport.mul_left.mul_right
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  have ht := tendsto_integral_regularizedDensityResidual hρ.1 hV.measurable
    hψ.measurable hc hC hM0 (fun x hx => (hb x hx).1)
    (fun x hx => (hb x hx).2.2.1) (fun x hx => (hb x hx).2.2.2)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hM x)
  have hext (f : E → ℝ) :
      (∫ x in ball (0 : E) χ.rOut, ψ x * f x) = ∫ x, ψ x * f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := χ.zero_of_le_dist (not_lt.mp hx)
    simp [ψ, hz]
  simpa only [hext] using ht

/-- The normalized point-source identity for an actual smooth Gauss metric.
The test is a genuine compactly supported native energy test. The geometric
normalization hypotheses are produced from g,p by NativeNormalDensity. -/
theorem native_cutoff_pointSource_test (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    (hρ0 : g.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (φ : EnergyTest g.leviCivitaData univ) :
    (∫ x, (-g.leviCivitaData.laplacian φ x +
      (g.leviCivitaData.scalarCurvature x / 8) * φ x) *
        (χ x * ‖x‖⁻¹) ∂g.volumeMeasure) =
      4 * Real.pi * φ 0 + ∫ x, φ x * nativeResidual g χ x ∂g.volumeMeasure := by
  let ρ := g.pullbackVolumeDensity id
  let V := fun x => g.leviCivitaData.scalarCurvature x / 8
  let ψ := fun x => φ x * χ x * ρ x
  let m := fun x => φ x * ρ x
  let Q := fun x => -g.leviCivitaData.laplacian φ x + V x * φ x
  let I := fun ε : ℝ => ∫ x, Q x * (χ x * potential ε x) ∂g.volumeMeasure
  have hρ := native_density_smooth_positive g
  have hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V :=
    g.leviCivitaData.contMDiff_scalarCurvature.div_const 8
  have hψ : Continuous ψ := (φ.smooth.continuous.mul χ.continuous).mul hρ.1.continuous
  have hψc : HasCompactSupport ψ := χ.hasCompactSupport.mul_left.mul_right
  have hm : Continuous m := φ.smooth.continuous.mul hρ.1.continuous
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  have hχ0 : χ (0 : E) = 1 := χ.one_of_mem_closedBall (by simpa using χ.rIn_pos.le)
  have hk : Tendsto (fun ε : ℝ => ∫ x : E, kernel ε x * ψ x) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * φ 0)) := by
    simpa only [ψ, ρ, hχ0, hρ0, mul_one] using tendsto_kernel_test hψ hM
  have hj := (tendsto_integral_cutoff_densityResidual g hzero χ φ.smooth.continuous).mono_left
    (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hc := (tendsto_integral_native_cutoffError g χ isOpen_univ (subset_univ _)
    hm.continuousOn).mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hj0 : Integrable (fun x : E => ψ x * densityResidual ρ V x) := by
    have h := (native_integrable_iff_density g _).mp
      (φ.memLp.integrable_mul (native_cutoffDensityResidual_memLp g hzero χ))
    convert h using 1
    ext x
    dsimp [ψ]
    ring
  have hc0 : Integrable (fun x : E => m x * singularCutoffError g χ x) := by
    have h := (native_integrable_iff_density g _).mp
      (φ.memLp.integrable_mul (memLp_singularCutoffError g χ))
    convert h using 1
    ext x
    dsimp [m]
    ring
  have hsplit0 : (∫ x, φ x * nativeResidual g χ x ∂g.volumeMeasure) =
      (∫ x : E, ψ x * densityResidual ρ V x) +
        ∫ x : E, m x * singularCutoffError g χ x := by
    rw [native_integral_eq_density]
    calc
      _ = ∫ x : E, ψ x * densityResidual ρ V x + m x * singularCutoffError g χ x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by unfold nativeResidual; dsimp [ψ, m, ρ, V]; ring
      _ = _ := integral_add hj0 hc0
  have heq (ε : ℝ) (hε : 0 < ε) :
      I ε = (∫ x : E, kernel ε x * ψ x) +
        ((∫ x : E, ψ x * regularizedDensityResidual ρ V ε x) +
          ∫ x : E, m x * cutoffError g χ ε x) := by
    have hU : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : E => χ x * potential ε x) :=
      (χ.contDiff.mul ((contDiff_potential hε).of_le le_top)).contMDiff
    have hUc : HasCompactSupport (fun x : E => χ x * potential ε x) :=
      χ.hasCompactSupport.mul_right
    have hK : Integrable (fun x : E => kernel ε x * ψ x) :=
      ((contDiff_kernel hε).continuous.mul hψ).integrable_of_hasCompactSupport hψc.mul_left
    have hJ : Integrable (fun x : E => ψ x * regularizedDensityResidual ρ V ε x) :=
      (hψ.mul (continuous_regularizedDensityResidual g hε)).integrable_of_hasCompactSupport
        hψc.mul_right
    have hC : Integrable (fun x : E => m x * cutoffError g χ ε x) :=
      (hm.mul (continuous_cutoffError g χ hε)).integrable_of_hasCompactSupport
        (compact_cutoffError g χ ε).mul_left
    calc
      I ε = ∫ x, φ x * (-g.leviCivitaData.laplacian
          (fun y => χ y * potential ε y) x + V x * (χ x * potential ε x))
            ∂g.volumeMeasure :=
        native_schrodinger_integral_comm g.leviCivitaData hV φ.smooth hU
          φ.hasCompactSupport hUc
      _ = ∫ x : E, kernel ε x * ψ x +
          (ψ x * regularizedDensityResidual ρ V ε x + m x * cutoffError g χ ε x) := by
        rw [native_integral_eq_density]
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only
        rw [show V x = g.leviCivitaData.scalarCurvature x / 8 from rfl,
          native_regularized_cutoff_source g hGauss χ hε]
        unfold regularizedNativeResidual
        dsimp [ψ, m, ρ, V]
        ring
      _ = _ := (integral_add hK (hJ.add hC)).trans
        (congrArg (fun t : ℝ => (∫ x : E, kernel ε x * ψ x) + t) (integral_add hJ hC))
  have hright := hk.add (hj.add hc)
  have hrightI : Tendsto I (𝓝[>] 0)
      (𝓝 (4 * Real.pi * φ 0 + ∫ x, φ x * nativeResidual g χ x ∂g.volumeMeasure)) := by
    rw [hsplit0]
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (heq ε hε).symm
  have heqU (ε : ℝ) : regularized (OpenPartialHomeomorph.refl E) χ ε =
      (fun x : E => χ x * potential ε x) := by
    funext x
    exact regularized_comp _ _ _ (mem_univ x)
  have heqS : singular (OpenPartialHomeomorph.refl E) χ =
      (fun x : E => χ x * ‖x‖⁻¹) := by
    funext x
    exact singular_comp _ _ (mem_univ x)
  have hleft := tendsto_integral_mul_regularized g (OpenPartialHomeomorph.refl E)
    contMDiffOn_id contMDiffOn_id χ (subset_univ _)
    (conformalLaplacian_test_memLp g φ)
  simp only [heqU, heqS] at hleft
  exact tendsto_nhds_unique hleft hrightI

#print axioms tendsto_integral_cutoff_densityResidual
#print axioms native_cutoff_pointSource_test

end Yamabe3.Analysis.GreenParametrix
