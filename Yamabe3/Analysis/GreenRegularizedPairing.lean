import Yamabe3.Analysis.GreenKernelL1
import Yamabe3.Analysis.GreenResidualPairing
import Yamabe3.Analysis.GreenChartPairing
import Yamabe3.Analysis.Green.NativeResidualSupport
import Yamabe3.Analysis.Green.NativeChartCutoffTransfer
import Yamabe3.Analysis.Green.NativeNormalDensity

/-!
# The native regularized point-source pairing with another singular function

A genuine native L2 function only has to be continuous at the pole under
consideration. It may have another Green singularity elsewhere. The exact
native operator is transferred through the actual chart, its normalized
kernel evaluates the continuous germ, and the actual residual converges by
its proved native L2 domination.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.RegularizedNewton
open Yamabe3.Parametrix
open Yamabe3.Analysis.ChartOperatorTransfer
open Yamabe3.Analysis.NormalCoordinates

/-- The actual regularized residual is native L2. The proof also covers the
harmless totalized parameter zero, because its domination was uniform. -/
theorem regularizedNativeResidual_memLp (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) :
    MemLp (regularizedNativeResidual g χ ε) 2 g.volumeMeasure := by
  obtain ⟨H, hH, hbound⟩ := exists_L2_dominator_regularizedNativeResidual g hzero χ
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass (by norm_num)
  apply hH.of_le (measurable_regularizedNativeResidual g χ ε).aestronglyMeasurable
  filter_upwards [g.volumeMeasure.ae_ne (0 : E)] with x hx
  exact (hbound ε x hx).trans (le_abs_self (H x))

/-- Multiplying a native L2 function by the actual compact cutoff and
native density gives a Lebesgue L1 multiplier. The kernel then sees its
actual point value, with normalization exactly 4π. -/
theorem tendsto_integral_cutoff_kernel_L2 (g : RiemannianMetric 3 E)
    (hρ0 : g.pullbackVolumeDensity id 0 = 1)
    (χ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 g.volumeMeasure) (hm : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun ε : ℝ => ∫ x, f x * (χ x * kernel ε x) ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (4 * Real.pi * f 0)) := by
  have hρ := native_density_smooth_positive g
  have hχ : MemLp (χ : E → ℝ) 2 g.volumeMeasure :=
    χ.continuous.memLp_of_hasCompactSupport χ.hasCompactSupport
  have hi := (native_integrable_iff_density g (fun x => f x * χ x)).mp
    (hf.integrable_mul hχ)
  have hlim := tendsto_kernel_test_of_L1_continuousAt hi
    ((hm.mul χ.continuous.measurable).mul hρ.1.continuous.measurable)
    ((hc.mul χ.continuous.continuousAt).mul hρ.1.continuous.continuousAt)
  have hχ0 : χ (0 : E) = 1 := χ.one_of_mem_closedBall (by simp [χ.rIn_pos.le])
  simp only [hχ0, hρ0, mul_one] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun ε => by
    dsimp only
    rw [native_integral_eq_density]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring

/-- The full actual coordinate operator has the asserted point-source
limit against every native L2 function continuous at the pole. -/
theorem tendsto_integral_regularizedP_L2 (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E, g.inner x x v = inner ℝ x v)
    (hρ0 : g.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 g.volumeMeasure) (hm : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun ε : ℝ => ∫ x, f x *
      (-g.leviCivitaData.laplacian (cutoffRegularized χ ε) x +
        (g.leviCivitaData.scalarCurvature x / 8) * cutoffRegularized χ ε x)
          ∂g.volumeMeasure) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * f 0 + ∫ x, f x * nativeResidual g χ x ∂g.volumeMeasure)) := by
  have hK := tendsto_integral_cutoff_kernel_L2 g hρ0 χ hf hm hc
  have hF : Tendsto (fun ε : ℝ => ∫ x, f x * regularizedNativeResidual g χ ε x ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (∫ x, f x * nativeResidual g χ x ∂g.volumeMeasure)) :=
    (tendsto_integral_regularizedNativeResidual_L2 g hzero χ hf).mono_left nhdsWithin_le_nhds
  apply (hK.add hF).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hχK : MemLp (fun x => χ x * kernel ε x) 2 g.volumeMeasure :=
    (χ.continuous.mul (contDiff_kernel hε).continuous).memLp_of_hasCompactSupport
      χ.hasCompactSupport.mul_right
  erw [← integral_add (hf.integrable_mul hχK)
    (hf.integrable_mul (regularizedNativeResidual_memLp g hzero χ ε))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.mul_apply]
    rw [show -g.leviCivitaData.laplacian (cutoffRegularized χ ε) x +
        (g.leviCivitaData.scalarCurvature x / 8) * cutoffRegularized χ ε x =
        χ x * kernel ε x + regularizedNativeResidual g χ ε x from
      native_regularized_cutoff_source g hGauss χ hε x]
    ring

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
/-- The actual conformal Laplacian is a local operator: its support stays
inside that of the actual function. No smoothness is being supplied as data. -/
theorem tsupport_native_conformalP_subset (g : RiemannianMetric 3 M) (f : M → ℝ) :
    tsupport (fun y => -g.leviCivitaData.laplacian f y +
      (g.leviCivitaData.scalarCurvature y / 8) * f y) ⊆ tsupport f := by
  apply (tsupport_add (f := _) (g := _)).trans
  apply union_subset
  · change tsupport (-(g.leviCivitaData.laplacian f)) ⊆ tsupport f
    rw [tsupport_neg]
    exact g.leviCivitaData.tsupport_laplacian_subset f
  · exact tsupport_mul_subset_right

omit [MeasurableSpace M] [BorelSpace M] in
/-- The global original-manifold operator is the genuine zero extension
of the coordinate operator; actual locality proves the part outside the
coordinate support. -/
theorem native_regularizedP_eq_coordinateExtension (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U : Set E} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (hcoeff : ∀ x ∈ U, gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (χ : ContDiffBump (0 : E)) (hχU : tsupport χ ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    (fun y => -g.leviCivitaData.laplacian (regularized e χ ε) y +
      (g.leviCivitaData.scalarCurvature y / 8) * regularized e χ ε y) =
      coordinateExtension e (fun x => -gE.leviCivitaData.laplacian
        (cutoffRegularized χ ε) x +
          (gE.leviCivitaData.scalarCurvature x / 8) * cutoffRegularized χ ε x) := by
  have hχs := hχU.trans hUs
  have hM := (tsupport_native_conformalP_subset g (regularized e χ ε)).trans
    (tsupport_regularized_subset e χ hχs ε)
  have hE := (tsupport_native_conformalP_subset gE (cutoffRegularized χ ε)).trans
    (tsupport_cutoffRegularized_subset χ ε)
  funext y
  by_cases hy : y ∈ e '' tsupport χ
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [coordinateExtension_comp_apply e _ (hχs hx)]
    exact regularized_conformalP_transfer g gE g.leviCivitaData gE.leviCivitaData
      e he hei hU hUs hcoeff χ hχs hε (hχU hx)
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hM h))]
    by_cases hyt : y ∈ e.target
    · rw [coordinateExtension_apply e _ hyt]
      symm
      apply image_eq_zero_of_notMem_tsupport (f := fun x =>
        -gE.leviCivitaData.laplacian (cutoffRegularized χ ε) x +
          (gE.leviCivitaData.scalarCurvature x / 8) * cutoffRegularized χ ε x)
      intro h
      apply hy
      exact ⟨e.symm y, hE h, e.right_inv hyt⟩
    · simp only [coordinateExtension, indicator_of_notMem hyt]

/-- Actual native point-source evaluation against a measurable L2 function
continuous at this pole, with no boundedness or smoothness premise elsewhere. -/
theorem tendsto_integral_native_regularizedP_L2 (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {U : Set E} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (hcoeff : ∀ x ∈ U, gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    (hρ0 : gE.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (hχU : tsupport χ ⊆ U)
    {h : M → ℝ} (hh : MemLp h 2 g.volumeMeasure) (hm : Measurable h)
    (hc : ContinuousAt h (e 0)) :
    Tendsto (fun ε : ℝ => ∫ y, h y *
      (-g.leviCivitaData.laplacian (regularized e χ ε) y +
        (g.leviCivitaData.scalarCurvature y / 8) * regularized e χ ε y)
          ∂g.volumeMeasure) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * h (e 0) +
        ∫ y, h y * coordinateExtension e (nativeResidual gE χ) y ∂g.volumeMeasure)) := by
  have hχs := hχU.trans hUs
  have hK : MeasurableSet (tsupport χ) := (isClosed_tsupport _).measurableSet
  have hdensity (x : E) (hx : x ∈ tsupport χ) :
      gE.pullbackVolumeDensity id x = g.pullbackVolumeDensity e x :=
    density_eq_of_coefficients_eq g gE e x (hcoeff x (hχU hx))
  let f : E → ℝ := (tsupport χ).indicator (h ∘ e)
  have hf : MemLp f 2 gE.volumeMeasure :=
    memLp_chart_indicator_native g gE e he hei hK hχs hdensity hm hh
  have hfm : Measurable f := measurable_chart_indicator e hK hχs hm
  have hcenter : (0 : E) ∈ tsupport χ := by rw [χ.tsupport_eq]; simp [χ.rOut_pos.le]
  have hfeq : f =ᶠ[𝓝 (0 : E)] h ∘ e := by
    filter_upwards [ball_mem_nhds (0 : E) χ.rOut_pos] with x hx
    exact indicator_of_mem (by rw [χ.tsupport_eq]; exact ball_subset_closedBall hx) _
  have hfc : ContinuousAt f 0 :=
    (hc.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds (hχs hcenter)))).congr_of_eventuallyEq hfeq
  have hlim := tendsto_integral_regularizedP_L2 gE hGauss hρ0 hzero χ hf hfm hfc
  have hf0 : f 0 = h (e 0) := hfeq.eq_of_nhds
  have hFs : tsupport (nativeResidual gE χ) ⊆ tsupport χ :=
    tsupport_nativeResidual_subset gE χ
  have hFlim : (∫ x, f x * nativeResidual gE χ x ∂gE.volumeMeasure) =
      ∫ y, h y * coordinateExtension e (nativeResidual gE χ) y ∂g.volumeMeasure := by
    rw [integral_mul_coordinateExtension_eq_native_measurable g gE e he hei
      (measurable_nativeResidual gE χ) (hFs.trans hχs)
      (fun x hx => hdensity x (hFs hx)) hm]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport χ
      · rw [show f x = h (e x) from indicator_of_mem hx _]
      · have hz := image_eq_zero_of_notMem_tsupport (fun ht => hx (hFs ht))
        simp only [hz, mul_zero]
  rw [hf0, hFlim] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hEs := (tsupport_native_conformalP_subset gE (cutoffRegularized χ ε)).trans
    (tsupport_cutoffRegularized_subset χ ε)
  have hEc : Continuous (fun x => -gE.leviCivitaData.laplacian
      (cutoffRegularized χ ε) x +
        (gE.leviCivitaData.scalarCurvature x / 8) * cutoffRegularized χ ε x) :=
    (gE.leviCivitaData.continuous_laplacian (contDiff_cutoffRegularized χ hε).contMDiff).neg.add
      ((gE.leviCivitaData.continuous_scalarCurvature.div_const 8).mul
        (contDiff_cutoffRegularized χ hε).continuous)
  have hOp (y : M) := congrFun
    (native_regularizedP_eq_coordinateExtension g gE e he hei hU hUs hcoeff χ hχU hε) y
  simp_rw [hOp]
  rw [integral_mul_coordinateExtension_eq_native_measurable g gE e he hei
    hEc.measurable (hEs.trans hχs) (fun x hx => hdensity x (hEs hx)) hm]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : x ∈ tsupport χ
    · rw [show f x = h (e x) from indicator_of_mem hx _]
    · have hz := image_eq_zero_of_notMem_tsupport (fun ht => hx (hEs ht))
      simp only [hz, mul_zero]

#print axioms regularizedNativeResidual_memLp
#print axioms tendsto_integral_cutoff_kernel_L2
#print axioms tendsto_integral_regularizedP_L2
#print axioms tsupport_native_conformalP_subset
#print axioms native_regularizedP_eq_coordinateExtension
#print axioms tendsto_integral_native_regularizedP_L2

end Yamabe3.Analysis.GreenParametrix
