import Yamabe3.Analysis.SphereBoundaryLayer
import Yamabe3.Analysis.EuclideanSphereTrace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!+# Actual radial thin layers and physical sphere flux

The space integral is over the genuine Euclidean annulus and uses the
derivative of the fixed smooth outward-increasing cutoff. Polar measure
and Fubini reduce it to the previously proved normalized one-dimensional
kernel. The continuous payload may later be the actual metric density,
lifting, and unnormalized radial derivative of one and the same function.
No Green formula or weak-conormal agreement is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace Yamabe3.Analysis.EuclideanSphereTrace

open SphereBoundaryLayer

theorem continuous_spherical_average {F : E → ℝ} (hF : Continuous F) :
    Continuous (fun s : ℝ => ∫ θ : S, F (s • (θ : E)) ∂angularVolume) := by
  have hm : Continuous (fun p : ℝ × S => p.1 • (p.2 : E)) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous (μ := angularVolume)
    (f := fun s θ => F (s • (θ : E))) (hF.comp hm)
    (isCompact_univ : IsCompact (univ : Set S))
  simpa only [Measure.restrict_univ] using h

/-- The exact polar change of variables retains the radial Jacobian and
the same cutoff derivative. The factor `F x / ‖x‖` is nonsingular on the
actual annulus because its inner radius is positive. -/
theorem integral_radial_layer_eq_spherical_average {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) {F : E → ℝ} (hF : Continuous F) :
    (∫ x in sphereTraceAnnulus r (r + ε),
      deriv (exteriorLayerProfile r ε) ‖x‖ * (F x / ‖x‖)) =
      ∫ s in Icc r (r + ε), deriv (exteriorLayerProfile r ε) s *
        (s * ∫ θ : S, F (s • (θ : E)) ∂angularVolume) := by
  let K := sphereTraceAnnulus r (r + ε)
  have hd := continuous_exteriorLayerProfile_deriv r ε
  have hc : ContinuousOn (fun x : E =>
      deriv (exteriorLayerProfile r ε) ‖x‖ * (F x / ‖x‖)) K := by
    apply (hd.comp continuous_norm).continuousOn.mul
    exact hF.continuousOn.div continuous_norm.continuousOn
      (fun x hx => ne_of_gt (hr.trans_le hx.1))
  have hi := hc.integrableOn_compact (μ := (volume : Measure E))
    (isCompact_sphereTraceAnnulus r (r + ε))
  rw [integral_sphereTraceAnnulus_native_polar hr hi]
  let J : S × ℝ → ℝ := fun p =>
    deriv (exteriorLayerProfile r ε) p.2 * (p.2 * F (p.2 • (p.1 : E)))
  have hJ : Continuous J :=
    (hd.comp continuous_snd).mul
      (continuous_snd.mul (hF.comp
        (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))))
  have hJi : Integrable J (angularVolume.prod (volume.restrict (Icc r (r + ε)))) := by
    have hh := hJ.continuousOn.integrableOn_compact
      (μ := angularVolume.prod volume)
      ((isCompact_univ : IsCompact (univ : Set S)).prod
        (isCompact_Icc : IsCompact (Icc r (r + ε))))
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using hh
  calc
    _ = ∫ θ : S, (∫ s : ℝ in Icc r (r + ε),
        deriv (exteriorLayerProfile r ε) s * (s * F (s • (θ : E)))) ∂angularVolume := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro θ
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      have hspos : 0 < s := hr.trans_le hs.1
      change s ^ 2 * (deriv (exteriorLayerProfile r ε) ‖s • (θ : E)‖ *
        (F (s • (θ : E)) / ‖s • (θ : E)‖)) = _
      rw [norm_sphereTrace_radial θ hspos.le]
      field_simp [hspos.ne']
      <;> ring
    _ = ∫ s in Icc r (r + ε), ∫ θ : S,
        deriv (exteriorLayerProfile r ε) s * (s * F (s • (θ : E))) ∂angularVolume :=
      integral_integral_swap hJi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      change (∫ θ : S, deriv (exteriorLayerProfile r ε) s *
        (s * F (s • (θ : E))) ∂angularVolume) = _
      rw [integral_const_mul, integral_const_mul]

/-- The actual space-layer integral converges to the same spherical
payload, with its physical radius factor. -/
theorem tendsto_integral_radial_layer {r : ℝ} (hr : 0 < r)
    {F : E → ℝ} (hF : Continuous F) :
    Tendsto (fun ε : ℝ => ∫ x in sphereTraceAnnulus r (r + ε),
      deriv (exteriorLayerProfile r ε) ‖x‖ * (F x / ‖x‖)) (𝓝[>] 0)
      (𝓝 (r * ∫ θ : S, F (r • (θ : E)) ∂angularVolume)) := by
  have hlim := tendsto_integral_layer_derivative r
    (continuous_id.mul (continuous_spherical_average hF))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_radial_layer_eq_spherical_average hr hε hF).symm

#print axioms integral_radial_layer_eq_spherical_average
#print axioms tendsto_integral_radial_layer

end Yamabe3.Analysis.EuclideanSphereTrace
