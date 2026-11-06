import Yamabe3.Analysis.Green.RegularizedNewton
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateTest
import PoincareLib.Geometry.Riemannian.Measure.Singleton
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# The actual chart cutoff of the regularized Newton potential

The functions below are explicit scalar functions on the original manifold:
inside the chart target they are `χ(e.symm y) * Φε(e.symm y)`, and outside
that target they are zero. Smoothness is derived from compact coordinate
support and the proved Euclidean kernel theorem. The singular value at the
pole uses the usual totalized real inverse, hence equals zero; convergence
is asserted away from the pole and almost everywhere for native volume.

This module does not claim a native point-source equation. That still needs
the native operator calculation, coordinate-volume transport and residual
limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Parametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

abbrev E := RegularizedNewton.E

def cutoffRegularized (χ : ContDiffBump (0 : E)) (ε : ℝ) : E → ℝ :=
  fun x => χ x * RegularizedNewton.potential ε x

def cutoffSingular (χ : ContDiffBump (0 : E)) : E → ℝ :=
  fun x => χ x * ‖x‖⁻¹

lemma potential_zero (x : E) : RegularizedNewton.potential 0 x = ‖x‖⁻¹ := by
  unfold RegularizedNewton.potential
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  rw [← Real.rpow_natCast_mul (norm_nonneg x) 2 (-(1 / 2 : ℝ))]
  norm_num
  exact Real.rpow_neg_one _

theorem cutoffRegularized_zero (χ : ContDiffBump (0 : E)) :
    cutoffRegularized χ 0 = cutoffSingular χ := by
  funext x
  simp only [cutoffRegularized, cutoffSingular, potential_zero]

theorem contDiff_cutoffRegularized (χ : ContDiffBump (0 : E)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (cutoffRegularized χ ε) :=
  χ.contDiff.mul ((RegularizedNewton.contDiff_potential hε).of_le le_top)

theorem hasCompactSupport_cutoffRegularized (χ : ContDiffBump (0 : E)) (ε : ℝ) :
    HasCompactSupport (cutoffRegularized χ ε) := χ.hasCompactSupport.mul_right

theorem hasCompactSupport_cutoffSingular (χ : ContDiffBump (0 : E)) :
    HasCompactSupport (cutoffSingular χ) := χ.hasCompactSupport.mul_right

theorem tsupport_cutoffRegularized_subset (χ : ContDiffBump (0 : E)) (ε : ℝ) :
    tsupport (cutoffRegularized χ ε) ⊆ tsupport χ := tsupport_mul_subset_left

theorem tsupport_cutoffSingular_subset (χ : ContDiffBump (0 : E)) :
    tsupport (cutoffSingular χ) ⊆ tsupport χ := tsupport_mul_subset_left

variable {M : Type*} [TopologicalSpace M]

def regularized (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) (ε : ℝ) : M → ℝ :=
  coordinateExtension e (cutoffRegularized χ ε)

def singular (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) : M → ℝ :=
  coordinateExtension e (cutoffSingular χ)

theorem regularized_zero (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) :
    regularized e χ 0 = singular e χ := by
  unfold regularized singular
  rw [cutoffRegularized_zero]

theorem regularized_apply (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (ε : ℝ) {y : M} (hy : y ∈ e.target) :
    regularized e χ ε y = χ (e.symm y) * RegularizedNewton.potential ε (e.symm y) :=
  coordinateExtension_apply e _ hy

theorem singular_apply (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    {y : M} (hy : y ∈ e.target) :
    singular e χ y = χ (e.symm y) * ‖e.symm y‖⁻¹ := coordinateExtension_apply e _ hy

theorem regularized_eq_zero_of_notMem (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) {y : M} (hy : y ∉ e.target) :
    regularized e χ ε y = 0 := indicator_of_notMem hy _

theorem singular_eq_zero_of_notMem (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) {y : M} (hy : y ∉ e.target) :
    singular e χ y = 0 := indicator_of_notMem hy _

theorem regularized_comp (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (ε : ℝ) {x : E} (hx : x ∈ e.source) :
    regularized e χ ε (e x) = χ x * RegularizedNewton.potential ε x :=
  coordinateExtension_comp_apply e _ hx

theorem singular_comp (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    {x : E} (hx : x ∈ e.source) : singular e χ (e x) = χ x * ‖x‖⁻¹ :=
  coordinateExtension_comp_apply e _ hx

theorem regularized_comp_eventuallyEq (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) {x : E} (hx : x ∈ e.source) :
    (fun z => regularized e χ ε (e z)) =ᶠ[𝓝 x] cutoffRegularized χ ε := by
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  exact regularized_comp e χ ε hz

theorem singular_comp_eventuallyEq (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) {x : E} (hx : x ∈ e.source) :
    (fun z => singular e χ (e z)) =ᶠ[𝓝 x] cutoffSingular χ := by
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  exact singular_comp e χ hz

theorem exists_bump_supported (e : OpenPartialHomeomorph E M) (h0 : (0 : E) ∈ e.source) :
    ∃ χ : ContDiffBump (0 : E), tsupport χ ⊆ e.source := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_source 0 h0
  let χ : ContDiffBump (0 : E) :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity,
      rIn_lt_rOut := by linarith }
  refine ⟨χ, ?_⟩
  rw [χ.tsupport_eq]
  exact (closedBall_subset_ball (by dsimp [χ]; linarith)).trans hball

theorem regularized_eq_potential_near_center (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) (ε : ℝ)
    {x : E} (hx : x ∈ closedBall 0 χ.rIn) :
    regularized e χ ε (e x) = RegularizedNewton.potential ε x := by
  have hxχ : x ∈ tsupport χ := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_closedBall χ.rIn_lt_rOut.le hx
  rw [regularized_comp e χ ε (hχ hxχ), χ.one_of_mem_closedBall hx, one_mul]

theorem singular_eq_inv_norm_near_center (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {x : E} (hx : x ∈ closedBall 0 χ.rIn) : singular e χ (e x) = ‖x‖⁻¹ := by
  have hxχ : x ∈ tsupport χ := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_closedBall χ.rIn_lt_rOut.le hx
  rw [singular_comp e χ (hχ hxχ), χ.one_of_mem_closedBall hx, one_mul]

theorem regularized_comp_eventuallyEq_potential (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) (ε : ℝ)
    {x : E} (hx : x ∈ ball 0 χ.rIn) :
    (fun z => regularized e χ ε (e z)) =ᶠ[𝓝 x] RegularizedNewton.potential ε := by
  filter_upwards [isOpen_ball.mem_nhds hx] with z hz
  exact regularized_eq_potential_near_center e χ hχ ε (ball_subset_closedBall hz)

theorem singular_comp_eventuallyEq_inv_norm (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {x : E} (hx : x ∈ ball 0 χ.rIn) :
    (fun z => singular e χ (e z)) =ᶠ[𝓝 x] fun z : E => ‖z‖⁻¹ := by
  filter_upwards [isOpen_ball.mem_nhds hx] with z hz
  exact singular_eq_inv_norm_near_center e χ hχ (ball_subset_closedBall hz)

section Support

variable [T2Space M]

theorem tsupport_regularized_subset (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) (ε : ℝ) :
    tsupport (regularized e χ ε) ⊆ e '' tsupport χ :=
  (tsupport_coordinateExtension_subset_image e (hasCompactSupport_cutoffRegularized χ ε)
    ((tsupport_cutoffRegularized_subset χ ε).trans hχ)).trans
      (image_mono (tsupport_cutoffRegularized_subset χ ε))

theorem tsupport_singular_subset (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    tsupport (singular e χ) ⊆ e '' tsupport χ :=
  (tsupport_coordinateExtension_subset_image e (hasCompactSupport_cutoffSingular χ)
    ((tsupport_cutoffSingular_subset χ).trans hχ)).trans
      (image_mono (tsupport_cutoffSingular_subset χ))

theorem hasCompactSupport_regularized (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) (ε : ℝ) :
    HasCompactSupport (regularized e χ ε) :=
  hasCompactSupport_coordinateExtension e (hasCompactSupport_cutoffRegularized χ ε)
    ((tsupport_cutoffRegularized_subset χ ε).trans hχ)

theorem hasCompactSupport_singular (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    HasCompactSupport (singular e χ) :=
  hasCompactSupport_coordinateExtension e (hasCompactSupport_cutoffSingular χ)
    ((tsupport_cutoffSingular_subset χ).trans hχ)

end Support

section Smooth

variable [T2Space M] [ChartedSpace E M]

theorem contMDiff_regularized (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {ε : ℝ} (hε : 0 < ε) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (regularized e χ ε) :=
  contMDiff_coordinateExtension e hei (contDiff_cutoffRegularized χ hε)
    (hasCompactSupport_cutoffRegularized χ ε) ((tsupport_cutoffRegularized_subset χ ε).trans hχ)

theorem contMDiffAt_singular (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {y : M} (hy : y ≠ e 0) : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (singular e χ) y := by
  by_cases hs : y ∈ tsupport (singular e χ)
  · have hyt : y ∈ e.target := by
      obtain ⟨x, hx, rfl⟩ := tsupport_singular_subset e χ hχ hs
      exact e.map_source (hχ hx)
    have hz : e.symm y ≠ 0 := by
      intro hz
      apply hy
      rw [← e.right_inv hyt, hz]
    have hc : ContDiffAt ℝ ∞ (cutoffSingular χ) (e.symm y) :=
      χ.contDiffAt.mul ((contDiffAt_norm ℝ hz).inv (norm_ne_zero_iff.mpr hz))
    apply ContMDiffAt.congr_of_eventuallyEq _ (coordinateExtension_eventuallyEq e _ hyt)
    exact hc.contMDiffAt.comp y (hei.contMDiffAt (e.open_target.mem_nhds hyt))
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_tsupport_iff_eventuallyEq.mp hs)

theorem contMDiffOn_singular (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (singular e χ) ({e 0}ᶜ : Set M) := by
  intro y hy
  exact (contMDiffAt_singular e hei χ hχ (by simpa using hy)).contMDiffWithinAt

end Smooth

theorem regularized_nonneg (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) (y : M) : 0 ≤ regularized e χ ε y := by
  by_cases hy : y ∈ e.target
  · rw [regularized_apply e χ ε hy]
    exact mul_nonneg χ.nonneg (RegularizedNewton.potential_nonneg ε _)
  · simp only [regularized_eq_zero_of_notMem e χ ε hy, le_refl]

theorem singular_nonneg (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (y : M) : 0 ≤ singular e χ y := by
  by_cases hy : y ∈ e.target
  · rw [singular_apply e χ hy]
    exact mul_nonneg χ.nonneg (inv_nonneg.mpr (norm_nonneg _))
  · simp only [singular_eq_zero_of_notMem e χ hy, le_refl]

theorem regularized_le_singular (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) (ε : ℝ) {y : M} (hy : y ≠ e 0) :
    regularized e χ ε y ≤ singular e χ y := by
  by_cases hyt : y ∈ e.target
  · have hz : e.symm y ≠ 0 := by
      intro hz
      apply hy
      rw [← e.right_inv hyt, hz]
    rw [regularized_apply e χ ε hyt, singular_apply e χ hyt]
    exact mul_le_mul_of_nonneg_left (RegularizedNewton.potential_le_inv_norm ε hz) χ.nonneg
  · simp only [regularized_eq_zero_of_notMem e χ ε hyt, singular_eq_zero_of_notMem e χ hyt,
      le_refl]

theorem tendsto_regularized (e : OpenPartialHomeomorph E M)
    (χ : ContDiffBump (0 : E)) {y : M} (hy : y ≠ e 0) :
    Tendsto (fun ε : ℝ => regularized e χ ε y) (𝓝 0) (𝓝 (singular e χ y)) := by
  by_cases hyt : y ∈ e.target
  · have hz : e.symm y ≠ 0 := by
      intro hz
      apply hy
      rw [← e.right_inv hyt, hz]
    simp only [regularized_apply e χ _ hyt, singular_apply e χ hyt]
    exact tendsto_const_nhds.mul (RegularizedNewton.tendsto_potential hz)
  · simp only [regularized_eq_zero_of_notMem e χ _ hyt, singular_eq_zero_of_notMem e χ hyt]
    exact tendsto_const_nhds

section NativeAlmostEverywhere

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- An actual native compact energy test, with no smoothness premise for the
regularized chart function beyond what is proved above. -/
def regularizedEnergyTest (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {ε : ℝ} (hε : 0 < ε) : EnergyTest g.leviCivitaData univ :=
  EnergyTest.ofCoordinates e hei (cutoffRegularized χ ε)
    (contDiff_cutoffRegularized χ hε) (hasCompactSupport_cutoffRegularized χ ε)
    (fun _ hx => ⟨hχ (tsupport_cutoffRegularized_subset χ ε hx), mem_univ _⟩)

omit [MeasurableSpace M] [BorelSpace M] in
theorem regularizedEnergyTest_coe (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {ε : ℝ} (hε : 0 < ε) :
    (regularizedEnergyTest g e hei χ hχ hε : M → ℝ) = regularized e χ ε := rfl

theorem tendsto_regularized_ae (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) :
    ∀ᵐ y ∂g.volumeMeasure,
      Tendsto (fun ε : ℝ => regularized e χ ε y) (𝓝 0) (𝓝 (singular e χ y)) := by
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass (by norm_num)
  filter_upwards [g.volumeMeasure.ae_ne (e 0)] with y hy
  exact tendsto_regularized e χ hy

theorem regularized_le_singular_ae (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) (ε : ℝ) :
    ∀ᵐ y ∂g.volumeMeasure, regularized e χ ε y ≤ singular e χ y := by
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass (by norm_num)
  filter_upwards [g.volumeMeasure.ae_ne (e 0)] with y hy
  exact regularized_le_singular e χ ε hy

theorem aestronglyMeasurable_singular (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    AEStronglyMeasurable (singular e χ) g.volumeMeasure := by
  apply aestronglyMeasurable_of_tendsto_ae (f := fun n : ℕ => regularized e χ (1 / (n + 1 : ℝ))) atTop
  · intro n
    exact (contMDiff_regularized e hei χ hχ (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))).continuous.aestronglyMeasurable
  · filter_upwards [tendsto_regularized_ae g e χ] with y hy
    exact hy.comp tendsto_one_div_add_atTop_nhds_zero_nat

end NativeAlmostEverywhere

end Yamabe3.Parametrix
