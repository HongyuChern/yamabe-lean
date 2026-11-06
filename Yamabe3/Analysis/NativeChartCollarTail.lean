import Yamabe3.Analysis.NativeRestrictedGradientEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Equicontinuity
import Yamabe3.Analysis.EuclideanSphereTrace
import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Native gradient tails and true chart-sphere null volume

The original completed-energy tail and geometric collar proofs are checked
in one actual compilation unit. Both complete proof blocks and all public
names are retained verbatim; NativeRestrictedGradientTail is a compatibility
import. The domain integral, original g-volume, literal chart density and
Euclidean sphere-null theorem remain the same. No boundary trace or weak
conormal is postulated, and no successful compilation is asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def restrictedGradientTailNormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] restrictedGradientTailNormedSpace

/-- Positivity survives completion of the same actual domain integral. -/
theorem nativeRestrictedGradientEnergy_nonneg
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (w : H1Zero g.leviCivitaData univ) :
    0 ≤ nativeRestrictedGradientEnergy g Ω w w := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f =>
    rw [nativeRestrictedGradientEnergy_coe]
    apply integral_nonneg
    intro x
    by_cases hz : g.leviCivitaData.gradient f x = 0
    · simp [hz]
    · exact (g.pos x _ hz).le

/-- A domain-independent continuity modulus for the diagonal restricted
energy. This permits completion before the domains shrink. -/
theorem nativeRestrictedGradientEnergy_diagonal_dist_le
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (v w : H1Zero g.leviCivitaData univ) :
    dist (nativeRestrictedGradientEnergy g Ω v v)
      (nativeRestrictedGradientEnergy g Ω w w) ≤
        ‖v - w‖ * (‖v‖ + ‖w‖) := by
  let B := nativeRestrictedGradientEnergy g Ω
  have hsub : B v v - B w w = B (v - w) v + B w (v - w) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    ring
  calc
    _ = ‖B (v - w) v + B w (v - w)‖ := by rw [dist_eq_norm, hsub]
    _ ≤ ‖B (v - w) v‖ + ‖B w (v - w)‖ := norm_add_le _ _
    _ ≤ ‖v - w‖ * ‖v‖ + ‖w‖ * ‖v - w‖ :=
      add_le_add (nativeRestrictedGradientEnergy_apply_norm_le g Ω _ _)
        (nativeRestrictedGradientEnergy_apply_norm_le g Ω _ _)
    _ = _ := by ring

/-- Genuine native H1 gradient energy tends to zero on any measurable
sequence of domains eventually avoiding almost every actual point. -/
theorem nativeRestrictedGradientEnergy_tendsto_zero
    (g : RiemannianMetric 3 M) (Ω : ℕ → Set M)
    (hΩ : ∀ n, MeasurableSet (Ω n))
    (hpoint : ∀ᵐ x ∂g.volumeMeasure, ∀ᶠ n in atTop, x ∉ Ω n)
    (w : H1Zero g.leviCivitaData univ) :
    Tendsto (fun n => nativeRestrictedGradientEnergy g (Ω n) w w) atTop (𝓝 0) := by
  have hequi : Equicontinuous
      (fun n (v : H1Zero g.leviCivitaData univ) =>
        nativeRestrictedGradientEnergy g (Ω n) v v) := by
    intro v
    have hc : Continuous (fun w : H1Zero g.leviCivitaData univ =>
        ‖v - w‖ * (‖v‖ + ‖w‖)) := by fun_prop
    have ht : Tendsto (fun w : H1Zero g.leviCivitaData univ =>
        ‖v - w‖ * (‖v‖ + ‖w‖)) (𝓝 v) (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_mul] using (hc.continuousAt (x := v)).tendsto
    exact Metric.equicontinuousAt_of_continuity_modulus
      (fun w : H1Zero g.leviCivitaData univ => ‖v - w‖ * (‖v‖ + ‖w‖)) ht
      (fun n (w : H1Zero g.leviCivitaData univ) => nativeRestrictedGradientEnergy g (Ω n) w w)
      (Eventually.of_forall fun w n => nativeRestrictedGradientEnergy_diagonal_dist_le g (Ω n) v w)
  induction w using Completion.induction_on with
  | hp =>
    exact hequi.isClosed_setOfPred_tendsto continuous_const
  | ih f =>
    simp only [nativeRestrictedGradientEnergy_coe]
    let G : M → ℝ := fun x => g.inner x
      (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient f x)
    have hGi : Integrable G g.volumeMeasure := f.integrable_gradient f
    have hlim : Tendsto (fun n => ∫ x, (Ω n).indicator G x ∂g.volumeMeasure)
        atTop (𝓝 (∫ _x : M, (0 : ℝ) ∂g.volumeMeasure)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => ‖G x‖)
      · intro n
        exact hGi.aestronglyMeasurable.indicator (hΩ n)
      · exact hGi.norm
      · intro n
        exact Eventually.of_forall fun x => by
          by_cases hx : x ∈ Ω n <;> simp [hx]
      · filter_upwards [hpoint] with x hx
        apply tendsto_const_nhds.congr'
        filter_upwards [hx] with n hn
        simp [hn]
    simpa only [integral_indicator (hΩ _), integral_zero, G] using hlim

#print axioms nativeRestrictedGradientEnergy_nonneg
#print axioms nativeRestrictedGradientEnergy_diagonal_dist_le
#print axioms nativeRestrictedGradientEnergy_tendsto_zero

end Yamabe3.Analysis


end -- close the original gradient-tail noncomputable section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold ENNReal

namespace Yamabe3.Analysis.EuclideanSphereTrace

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The original metric's native ambient volume of the actual chart
sphere is zero. Its induced two-dimensional area is a different measure. -/
theorem native_chart_sphere_volume_zero
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (a : ℝ) (hs : sphere (0 : E) a ⊆ e.source) :
    g.volumeMeasure (e '' sphere (0 : E) a) = 0 := by
  rw [g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei
    isClosed_sphere.measurableSet hs]
  have hz : (volume : Measure E).restrict (sphere (0 : E) a) = 0 :=
    Measure.restrict_eq_zero.mpr (Measure.addHaar_sphere (volume : Measure E) (0 : E) a)
  simp only [hz, lintegral_zero_measure]

/-- The actual shrinking closed collars eventually avoid almost every
point for the original native volume. No boundary trace assertion is used. -/
theorem native_chart_collar_eventually_avoids_ae
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a : ℝ} (ha : 0 < a)
    (hKs : sphereTraceAnnulus a (2 * a) ⊆ e.source)
    (δ : ℕ → ℝ) (hδa : ∀ n, 2 * δ n ≤ a) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ᵐ y ∂g.volumeMeasure, ∀ᶠ n in atTop,
      y ∉ e '' sphereTraceAnnulus a (a + 2 * δ n) := by
  have hsub (n : ℕ) : sphereTraceAnnulus a (a + 2 * δ n) ⊆ sphereTraceAnnulus a (2 * a) := by
    intro x hx
    exact ⟨hx.1, by linarith only [hx.2, hδa n]⟩
  have hs : sphere (0 : E) a ⊆ e.source := by
    intro x hx
    have hn : ‖x‖ = a := by simpa only [mem_sphere, dist_zero_right] using hx
    apply hKs
    exact ⟨by rw [hn], by rw [hn]; linarith⟩
  have hnull := native_chart_sphere_volume_zero g e he hei a hs
  have hae : ∀ᵐ y ∂g.volumeMeasure, y ∉ e '' sphere (0 : E) a := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hae] with y hy
  by_cases hyK : y ∈ e '' sphereTraceAnnulus a (2 * a)
  · rcases hyK with ⟨x, hx, rfl⟩
    have hxa : a < ‖x‖ := by
      apply lt_of_le_of_ne hx.1
      intro hEq
      apply hy
      exact mem_image_of_mem e (by simpa only [mem_sphere, dist_zero_right] using hEq.symm)
    have hsmall : ∀ᶠ n in atTop, 2 * δ n < ‖x‖ - a :=
      (hδ.const_mul 2).eventually (eventually_lt_nhds (by simpa using sub_pos.mpr hxa))
    filter_upwards [hsmall] with n hn
    rintro ⟨z, hz, hzx⟩
    have heq : z = x := e.injOn (hKs (hsub n hz)) (hKs hx) hzx
    subst z
    linarith only [hz.2, hn]
  · apply Eventually.of_forall
    intro n hn
    rcases hn with ⟨x, hx, rfl⟩
    exact hyK ⟨x, hsub n hx, rfl⟩

/-- Native gradient energy of the same completed H1 element vanishes in
the actual shrinking chart collars. -/
theorem native_chart_collar_gradient_energy_tendsto_zero
    [CompactSpace M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a : ℝ} (ha : 0 < a)
    (hKs : sphereTraceAnnulus a (2 * a) ⊆ e.source)
    (δ : ℕ → ℝ) (hδa : ∀ n, 2 * δ n ≤ a) (hδ : Tendsto δ atTop (𝓝 0))
    (w : H1Zero g.leviCivitaData univ) :
    Tendsto (fun n => nativeRestrictedGradientEnergy g
      (e '' sphereTraceAnnulus a (a + 2 * δ n)) w w) atTop (𝓝 0) := by
  apply nativeRestrictedGradientEnergy_tendsto_zero g
    (fun n => e '' sphereTraceAnnulus a (a + 2 * δ n)) _
    (native_chart_collar_eventually_avoids_ae g e he hei ha hKs δ hδa hδ) w
  intro n
  have hsource : sphereTraceAnnulus a (a + 2 * δ n) ⊆ e.source := by
    intro x hx
    exact hKs ⟨hx.1, by linarith only [hx.2, hδa n]⟩
  exact ((isCompact_sphereTraceAnnulus a (a + 2 * δ n)).image_of_continuousOn
    (e.continuousOn.mono hsource)).measurableSet

#print axioms native_chart_sphere_volume_zero
#print axioms native_chart_collar_eventually_avoids_ae
#print axioms native_chart_collar_gradient_energy_tendsto_zero

end Yamabe3.Analysis.EuclideanSphereTrace


end -- close the original chart-collar noncomputable section
