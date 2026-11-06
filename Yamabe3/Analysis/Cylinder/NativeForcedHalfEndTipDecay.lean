import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndPhysicalL2

/-!
# The same original physical field has quantitative decay at the puncture

The literal time mask `1_(T,infinity)` of the same joint representative
is exactly the spatial mask of the ball of radius `exp(-T)`, including
zero.  The existing genuine polar/Fubini producer needs no continuity
of the masked Hilbert curve.  It therefore yields the exact tail square
integral and actual L2 membership of the original field on this ball.

For the original forced inverse, its already proved `exp(-2t)` norm
bound leaves the integrable majorant `C0^2 * norm(F)^2 * exp(-6t)`.
The exact tail integral is `exp(-6T)/6`.  No physical integrability or
boundary trace is assumed, and no physical representative is replaced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

/-- The time tail mask is the exact pointwise spatial ball mask of the
same lift.  The retained origin value is handled separately. -/
theorem native_cylinderLift_time_tail_indicator
    (T : ℝ) (w : ℝ × S → ℝ) :
    cylinderLift (fun p : ℝ × S =>
      ((Ioi T).indicator (fun _ : ℝ => (1 : ℝ)) p.1) * w p) =
      (Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)}).indicator (cylinderLift w) := by
  funext x
  by_cases hx : x = 0
  · subst x
    have hnot : (0 : E) ∉ Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)} := by
      simp
    rw [cylinderLift_zero, Set.indicator_of_notMem hnot]
  · let y : puncturedSpace := ⟨x, by change x ≠ 0; exact hx⟩
    have hlog : T < -Real.log ‖x‖ ↔ ‖x‖ < Real.exp (-T) := by
      calc
        T < -Real.log ‖x‖ ↔ Real.log ‖x‖ < -T := by
          constructor <;> intro h <;> linarith only [h]
        _ ↔ ‖x‖ < Real.exp (-T) := Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx)
    have hball : x ∈ Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)} ↔
        T < -Real.log ‖x‖ := by
      simpa only [Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
        Set.mem_singleton_iff, hx, not_false_eq_true, and_true] using hlog.symm
    change cylinderLift (fun p : ℝ × S =>
      ((Ioi T).indicator (fun _ : ℝ => (1 : ℝ)) p.1) * w p) (y : E) =
      (Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)}).indicator (cylinderLift w) (y : E)
    by_cases ht : T < -Real.log ‖x‖
    · rw [Set.indicator_of_mem (hball.mpr ht), cylinderLift_coe, cylinderLift_coe w y]
      change radialScale ‖x‖ *
        (((Ioi T).indicator (fun _ : ℝ => (1 : ℝ)) (-Real.log ‖x‖)) *
          w (-Real.log ‖x‖, sphereDirection y)) =
        radialScale ‖x‖ * w (-Real.log ‖x‖, sphereDirection y)
      rw [Set.indicator_of_mem (show -Real.log ‖x‖ ∈ Ioi T from ht), one_mul]
    · rw [Set.indicator_of_notMem (fun h => ht (hball.mp h)), cylinderLift_coe]
      change radialScale ‖x‖ *
        (((Ioi T).indicator (fun _ : ℝ => (1 : ℝ)) (-Real.log ‖x‖)) *
          w (-Real.log ‖x‖, sphereDirection y)) = 0
      rw [Set.indicator_of_notMem (show -Real.log ‖x‖ ∉ Ioi T from ht), zero_mul, mul_zero]

/-- The exact polar square identity and L2 membership on a strict tip
ball.  Only the true weighted Hilbert tail is an integrability input;
the discontinuous time mask does not require a continuous curve. -/
theorem native_halfEnd_lift_tip_memLp_of_weighted_integrable
    (T : ℝ) (hT : 0 ≤ T)
    {U : ℝ → AngularL2} {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    (htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi T)) :
    MemLp (cylinderLift w) 2
      (volume.restrict (Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)})) ∧
    (∫ x in Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)}, cylinderLift w x ^ 2) =
      ∫ t in Ioi T, Real.exp (-2 * t) * ‖U t‖ ^ 2 := by
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let OT := Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)}
  let a : ℝ → ℝ := (Ioi T).indicator (fun _ : ℝ => (1 : ℝ))
  let H : ℝ → AngularL2 := fun t => a t • U t
  let zT : ℝ × S → ℝ := fun p => a p.1 * w p
  have hOT : MeasurableSet OT := (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hradius : Real.exp (-T) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hT)
  have hsubset : OT ⊆ O := by
    intro x hx
    exact ⟨lt_of_lt_of_le hx.1 hradius, hx.2⟩
  have htimesubset : Ioi T ⊆ Ioi (0 : ℝ) := fun _ ht => hT.trans_lt ht
  have ha : Measurable a := measurable_const.indicator measurableSet_Ioi
  have hzT : Measurable zT := (ha.comp measurable_fst).mul hw
  have hAE (t : ℝ) : (fun θ => zT (t, θ)) =ᵐ[angularVolume] (H t : S → ℝ) := by
    have hcoerce := (ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul (a t) (U t))
    filter_upwards [hae t, hcoerce] with θ hθ hc
    change a t * w (t, θ) = ((a t • U t : AngularL2) : S → ℝ) θ
    rw [hθ]
    simpa only [Pi.smul_apply, smul_eq_mul] using (hc (mem_univ θ)).symm
  have hweight : (fun t : ℝ => Real.exp (-2 * t) * ‖H t‖ ^ 2) =
      (Ioi T).indicator (fun t : ℝ => Real.exp (-2 * t) * ‖U t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Ioi T
    · simp only [H, a, Set.indicator_of_mem ht, one_smul]
    · simp only [H, a, Set.indicator_of_notMem ht, zero_smul, norm_zero,
        pow_two, zero_mul, mul_zero]
  have htimeH : IntegrableOn (fun t => Real.exp (-2 * t) * ‖H t‖ ^ 2) (Ioi 0) := by
    rw [hweight]
    exact (IntegrableOn.integrable_indicator htime measurableSet_Ioi).integrableOn
  obtain ⟨hmaskLp, hmaskIntegral⟩ :=
    native_halfEnd_lift_memLp_of_weighted_integrable hzT hAE htimeH
  have hphysical : cylinderLift zT = OT.indicator (cylinderLift w) :=
    native_cylinderLift_time_tail_indicator T w
  change MemLp (cylinderLift zT) 2 (volume.restrict O) at hmaskLp
  rw [hphysical] at hmaskLp
  have htipLp := (memLp_indicator_iff_restrict hOT).mp hmaskLp
  rw [Measure.restrict_restrict_of_subset hsubset] at htipLp
  have hphysicalSq : (fun x : E => cylinderLift zT x ^ 2) =
      OT.indicator (fun x : E => cylinderLift w x ^ 2) := by
    funext x
    rw [hphysical]
    by_cases hx : x ∈ OT
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, pow_two, zero_mul]
  refine ⟨htipLp, ?_⟩
  calc
    _ = ∫ x in O, cylinderLift zT x ^ 2 := by
      rw [hphysicalSq, setIntegral_indicator hOT, inter_eq_right.mpr hsubset]
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * ‖H t‖ ^ 2 := hmaskIntegral
    _ = ∫ t in Ioi T, Real.exp (-2 * t) * ‖U t‖ ^ 2 := by
      rw [hweight, setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr htimesubset]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The original forced solution has its actual tip L2 square integral
bounded by the exact `exp(-6T)/6` tail of the original source estimate. -/
theorem native_forced_halfEnd_value_tip_memLp
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp (cylinderLift w) 2
      (volume.restrict (Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)})) ∧
      (∫ x in Metric.ball (0 : E) (Real.exp (-T)) \ {(0 : E)}, cylinderLift w x ^ 2) ≤
        (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 * ‖F‖ ^ 2 *
          Real.exp (-6 * T) / 6 := by
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let B : ℝ := (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖
  have hU : Continuous U := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have hbound (t : ℝ) : ‖U t‖ ≤ Real.exp (-2 * t) * B :=
    nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 V hV hV0 F t
  have hmajor : IntegrableOn (fun t : ℝ => B ^ 2 * Real.exp (-6 * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-6 : ℝ) < 0) T).const_mul (B ^ 2)
  have hle (t : ℝ) : Real.exp (-2 * t) * ‖U t‖ ^ 2 ≤ B ^ 2 * Real.exp (-6 * t) := by
    calc
      _ ≤ Real.exp (-2 * t) * (Real.exp (-2 * t) * B) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2) (Real.exp_pos _).le
      _ = B ^ 2 * (Real.exp (-2 * t) * Real.exp (-2 * t) * Real.exp (-2 * t)) := by ring
      _ = B ^ 2 * Real.exp (-6 * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have htime : IntegrableOn (fun t => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioi T) := by
    apply hmajor.mono'
      (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
        (hU.norm.pow 2)).aestronglyMeasurable.restrict)
    filter_upwards [] with t
    change ‖Real.exp (-2 * t) * ‖U t‖ ^ 2‖ ≤ B ^ 2 * Real.exp (-6 * t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hle t
  obtain ⟨hmem, he⟩ :=
    native_halfEnd_lift_tip_memLp_of_weighted_integrable T hT hw hwAE htime
  refine ⟨hmem, ?_⟩
  rw [he]
  calc
    _ ≤ ∫ t in Ioi T, B ^ 2 * Real.exp (-6 * t) :=
      setIntegral_mono_on htime hmajor measurableSet_Ioi (fun t _ht => hle t)
    _ = B ^ 2 * Real.exp (-6 * T) / 6 := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-6 : ℝ) < 0) T]
      ring
    _ = _ := by dsimp only [B]; ring

#print axioms native_cylinderLift_time_tail_indicator
#print axioms native_halfEnd_lift_tip_memLp_of_weighted_integrable
#print axioms native_forced_halfEnd_value_tip_memLp

end Yamabe3.Analysis.SpherePolar
