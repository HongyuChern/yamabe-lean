import Yamabe3.Analysis.Cylinder.NativePolarMeasure

/-!
# The actual logarithmic polar product integral

Integrability is transferred in both directions using the genuine polar
homeomorphism and the one-dimensional exponential Jacobian. The final
formula has time first and native induced-sphere volume second, as in the
actual Hilbert-valued cylinder equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Yamabe3.Analysis.SpherePolar

def logPolarWeight (f : E → ℝ) (p : S × ℝ) : ℝ :=
  Real.exp (-3 * p.2) * f (Real.exp (-p.2) • (p.1 : E))

def logCylinderWeight (f : E → ℝ) (p : ℝ × S) : ℝ :=
  Real.exp (-3 * p.1) * f (Real.exp (-p.1) • (p.2 : E))

theorem measurable_logPolarWeight {f : E → ℝ} (hf : Measurable f) :
    Measurable (logPolarWeight f) := by
  apply Measurable.mul (by fun_prop)
  exact hf.comp (by fun_prop)

theorem measurable_logCylinderWeight {f : E → ℝ} (hf : Measurable f) :
    Measurable (logCylinderWeight f) :=
  (measurable_logPolarWeight hf).comp measurable_swap

theorem integrable_euclidean_iff_logPolar {f : E → ℝ} (hf : Measurable f) :
    Integrable f ↔ Integrable (logPolarWeight f) (angularVolume.prod volume) := by
  have hP : AEStronglyMeasurable
      (fun p : S × Ioi (0 : ℝ) => f (p.2.1 • (p.1 : E)))
      (angularVolume.prod (Measure.volumeIoiPow 2)) :=
    (hf.comp (by fun_prop)).aestronglyMeasurable
  have hL := (measurable_logPolarWeight hf).aestronglyMeasurable
    (μ := angularVolume.prod volume)
  rw [integrable_euclidean_iff_polar, integrable_prod_iff hP, integrable_prod_iff hL]
  have hi (θ : S) :
      Integrable (fun r : Ioi (0 : ℝ) => f (r.1 • (θ : E))) (Measure.volumeIoiPow 2) ↔
      Integrable (fun t : ℝ => logPolarWeight f (θ, t)) :=
    integrable_radius_log_iff (fun r => f (r • (θ : E)))
  have hn (θ : S) :
      (∫ r : Ioi (0 : ℝ), ‖f (r.1 • (θ : E))‖ ∂Measure.volumeIoiPow 2) =
        ∫ t : ℝ, ‖logPolarWeight f (θ, t)‖ := by
    rw [integral_radius_log (fun r => ‖f (r • (θ : E))‖)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [logPolarWeight, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs.mono (fun θ hθ => (hi θ).mp hθ), ?_⟩
    simpa only [hn] using hb
  · rintro ⟨hs, hb⟩
    refine ⟨hs.mono (fun θ hθ => (hi θ).mpr hθ), ?_⟩
    simpa only [hn] using hb

theorem integrable_euclidean_iff_cylinder {f : E → ℝ} (hf : Measurable f) :
    Integrable f ↔ Integrable (logCylinderWeight f) (volume.prod angularVolume) := by
  rw [integrable_euclidean_iff_logPolar hf]
  exact integrable_swap_iff.symm

theorem integral_euclidean_eq_cylinder {f : E → ℝ}
    (hf : Measurable f) (hi : Integrable f) :
    (∫ x : E, f x) =
      ∫ t : ℝ, ∫ θ : S, Real.exp (-3 * t) * f (Real.exp (-t) • (θ : E))
        ∂angularVolume := by
  calc
    _ = ∫ θ : S, ∫ r : Ioi (0 : ℝ), f (r.1 • (θ : E))
        ∂Measure.volumeIoiPow 2 ∂angularVolume := integral_native_polar f hi
    _ = ∫ θ : S, ∫ t : ℝ, logPolarWeight f (θ, t) ∂volume ∂angularVolume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun θ =>
        integral_radius_log (fun r => f (r • (θ : E)))
    _ = _ := integral_integral_swap ((integrable_euclidean_iff_logPolar hf).mp hi)

/-- A measurable Euclidean integrand is integrable as soon as its actual
weighted cylinder pullback is integrable. This direction will provide the
legitimate physical test pairings from locally L2 cylinder solutions. -/
theorem integral_euclidean_eq_cylinder_of_pullback {f : E → ℝ}
    (hf : Measurable f)
    (hi : Integrable (logCylinderWeight f) (volume.prod angularVolume)) :
    (∫ x : E, f x) =
      ∫ t : ℝ, ∫ θ : S, logCylinderWeight f (t, θ) ∂angularVolume :=
  integral_euclidean_eq_cylinder hf ((integrable_euclidean_iff_cylinder hf).mpr hi)

#print axioms integrable_euclidean_iff_cylinder
#print axioms integral_euclidean_eq_cylinder_of_pullback

end Yamabe3.Analysis.SpherePolar
