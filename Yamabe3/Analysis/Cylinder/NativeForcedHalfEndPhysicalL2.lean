import Yamabe3.Analysis.NativeForcedHalfEnd
import Yamabe3.Analysis.Cylinder.NativeHalfEndPhysicalForcing

/-!
# Global physical L2 estimates for the constructed forced half-end

The same actual native Dirichlet curve supplies the original physical
function.  Its exp(-2t) decay, together with the exact logarithmic polar
weight exp(-2t), gives the genuine physical square-integral factor 1/6.
The original high projected source supplies its actual physical source
with the coefficient-eight square-integral factor 32.

The hypotheses on joint measurable representatives only identify the
already constructed Hilbert curves.  No PDE, physical L2 estimate,
gradient estimate, or stronger source regularity is an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- The exact polar measure turns an actual exp(-2t) angular norm bound
into an original physical L2 bound with factor 1/6. -/
theorem native_halfEnd_lift_memLp_of_expNegTwo_bound
    {U : ℝ → AngularL2} (hU : Continuous U)
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (B : ℝ) (hbound : ∀ t, 0 ≤ t → ‖U t‖ ≤ Real.exp (-2 * t) * B) :
    MemLp (cylinderLift w) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift w x ^ 2) ≤ B ^ 2 / 6 := by
  have hmajorant : IntegrableOn (fun t : ℝ => B ^ 2 * Real.exp (-6 * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-6 : ℝ) < 0) 0).const_mul (B ^ 2)
  have hle (t : ℝ) (ht : 0 < t) :
      Real.exp (-2 * t) * ‖U t‖ ^ 2 ≤ B ^ 2 * Real.exp (-6 * t) := by
    calc
      _ ≤ Real.exp (-2 * t) * (Real.exp (-2 * t) * B) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hbound t ht.le) 2) (Real.exp_pos _).le
      _ = B ^ 2 * (Real.exp (-2 * t) * Real.exp (-2 * t) * Real.exp (-2 * t)) := by ring
      _ = B ^ 2 * Real.exp (-6 * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi 0) := by
    apply hmajorant.mono'
      (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
        (hU.norm.pow 2)).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖Real.exp (-2 * t) * ‖U t‖ ^ 2‖ ≤ B ^ 2 * Real.exp (-6 * t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hle t ht
  obtain ⟨hlift, he⟩ := native_halfEnd_lift_memLp_of_weighted_integrable hw hae htime
  refine ⟨hlift, ?_⟩
  rw [he]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), B ^ 2 * Real.exp (-6 * t) :=
      setIntegral_mono_on htime hmajorant measurableSet_Ioi (fun t ht => hle t ht)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-6 : ℝ) < 0) 0]
      norm_num <;> ring

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- Global original physical L2 membership and quantitative estimate
are consequences of the actual same-potential Dirichlet inverse. -/
theorem native_forced_halfEnd_value_global_memLp
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) :
    MemLp (cylinderLift w) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)}, cylinderLift w x ^ 2) ≤
        (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 * ‖F‖ ^ 2 / 6 := by
  simpa only [mul_pow] using native_halfEnd_lift_memLp_of_expNegTwo_bound
    (nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F) hw hwAE
    ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖)
    (fun t _ht => nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 V hV hV0 F t)

/-- The original high projected source supplies its actual physical L2
forcing on the whole punctured unit ball, without a supplied bound. -/
theorem native_forced_halfEnd_source_global_memLp
    (F : ℝ≥0 →ᵇ AngularL2) {z : ℝ × S → ℝ} (hz : Measurable z)
    (hzAE : ∀ t, (fun θ => z (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    MemLp (physicalForcing (fun p => Real.exp (-2 * p.1) * z p)) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
        physicalForcing (fun p => Real.exp (-2 * p.1) * z p) x ^ 2) ≤ 32 * ‖F‖ ^ 2 := by
  apply native_halfEnd_physicalForcing_memLp
    (nativeHighProjection.continuous.comp (F.continuous.comp continuous_real_toNNReal)) hz hzAE
  intro t _ht
  exact (nativeAngularProjection_apply_norm_le _ (F t.toNNReal)).trans
    (F.norm_coe_le_norm t.toNNReal)

#print axioms native_halfEnd_lift_memLp_of_expNegTwo_bound
#print axioms native_forced_halfEnd_value_global_memLp
#print axioms native_forced_halfEnd_source_global_memLp

end Yamabe3.Analysis.SpherePolar
