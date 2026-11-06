import Yamabe3.Analysis.Cylinder.NativePuncturedUnitBallCutoff
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndBoundaryDecay
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndTipDecay
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndGlobalGradient
import Yamabe3.Analysis.UniformElliptic.NativeWeakH1CutoffClosure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual zero-boundary Sobolev membership of the original forced field

The fixed smooth cutoff is applied to the same original physical function.
Its actual derivative is supported in the two squared-radius layers.
The inner closed layer is put in the strictly larger open ball of squared
radius `3*epsilon`.  The outer closed layer lies in the genuine closed
logarithmic shell `[0,4*epsilon]`.  Thus no spherical endpoint is discarded.

The original tip and entrance estimates give cubic square mass in both
layers.  The one cutoff constant `K/epsilon` consequently gives an actual
product-rule error of squared L2 size at most a fixed constant times
epsilon.  Integrability is proved before every integral comparison.
Taking epsilon equal to `1/(n+5)` proves the error convergence required
by the actual weak Sobolev cutoff closure theorem.  The original global
H1 witness then produces `MemH01` for the same `cylinderLift w`.

This is the weak Sobolev approximation predicate on the punctured open
unit ball.  No conormal identity or boundary Green formula is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

private def cutoffTipTime (ε : ℝ) : ℝ := -Real.log (3 * ε) / 2

private theorem cutoffTipTime_nonneg (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    0 ≤ cutoffTipTime ε := by
  have hl : Real.log (3 * ε) ≤ 0 :=
    Real.log_nonpos (by positivity) (by linarith)
  dsimp only [cutoffTipTime]
  linarith

private theorem cutoffTipTime_radius_sq (ε : ℝ) (hε : 0 < ε) :
    Real.exp (-cutoffTipTime ε) ^ 2 = 3 * ε := by
  calc
    _ = Real.exp (2 * (-cutoffTipTime ε)) := by
      simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (-cutoffTipTime ε) 2).symm
    _ = Real.exp (Real.log (3 * ε)) := by
      congr 1
      dsimp only [cutoffTipTime]
      ring
    _ = _ := Real.exp_log (by positivity)

private theorem cutoffTipTime_exp_six (ε : ℝ) (hε : 0 < ε) :
    Real.exp (-6 * cutoffTipTime ε) = (3 * ε) ^ 3 := by
  calc
    _ = Real.exp (3 * Real.log (3 * ε)) := by
      congr 1
      dsimp only [cutoffTipTime]
      ring
    _ = Real.exp (Real.log (3 * ε)) ^ 3 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (3 * ε)) 3
    _ = _ := by rw [Real.exp_log (by positivity : 0 < 3 * ε)]

private theorem cutoff_inner_mem_tip (ε : ℝ) (hε : 0 < ε)
    {x : E} (hx : x ∈ Metric.ball (0 : E) 1 \ {(0 : E)})
    (hinner : ‖x‖ ^ 2 ≤ 2 * ε) :
    x ∈ Metric.ball (0 : E) (Real.exp (-cutoffTipTime ε)) \ {(0 : E)} := by
  refine ⟨?_, hx.2⟩
  rw [Metric.mem_ball, dist_zero_right]
  apply (sq_lt_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [cutoffTipTime_radius_sq ε hε]
  linarith

private theorem cutoff_outer_mem_shell (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    {x : E} (hx : x ∈ Metric.ball (0 : E) 1 \ {(0 : E)})
    (houter : 1 - 2 * ε ≤ ‖x‖ ^ 2) : x ∈ cylinderShell 0 (4 * ε) := by
  have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hr1 : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  have hsq : ‖x‖ ^ 2 ≤ ‖x‖ := by
    nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hr1.le)]
  have hrhalf : 1 / 2 ≤ ‖x‖ := by linarith
  have hepsr : 2 * ε ≤ 4 * ε * ‖x‖ := by
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hrhalf)]
  have hinv : ‖x‖⁻¹ - 1 ≤ 4 * ε := by
    have hquot : 1 / ‖x‖ ≤ 1 + 4 * ε := by
      apply (div_le_iff₀ hr).mpr
      nlinarith
    simpa only [one_div] using (by linarith : 1 / ‖x‖ - 1 ≤ 4 * ε)
  have hlog : -Real.log ‖x‖ ≤ 4 * ε := by
    calc
      _ = Real.log ‖x‖⁻¹ := (Real.log_inv _).symm
      _ ≤ ‖x‖⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
      _ ≤ _ := hinv
  change Real.exp (-(4 * ε)) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp (-0)
  constructor
  · calc
      _ ≤ Real.exp (Real.log ‖x‖) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hr
  · simpa only [neg_zero, Real.exp_zero] using hr1.le

private theorem cutoff_coordinate_bound (ε : ℝ) (K : ℝ)
    (hK : ∀ x : E, ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ ≤ K / ε)
    (j : Fin 3) (x : E) :
    ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x (EuclideanSpace.single j 1)‖ ≤ K / ε := by
  calc
    _ ≤ ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ *
        ‖EuclideanSpace.single j (1 : ℝ)‖ :=
      (fderiv ℝ (nativePuncturedUnitBallCutoff ε) x).le_opNorm _
    _ = ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ := by simp
    _ ≤ _ := hK x

private theorem cutoff_error_memLp {u : E → ℝ}
    (hu : MemLp u 2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})))
    (ε K : ℝ)
    (hK : ∀ x : E, ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ ≤ K / ε)
    (j : Fin 3) :
    MemLp (fun x => fderiv ℝ (nativePuncturedUnitBallCutoff ε) x
      (EuclideanSpace.single j 1) * u x) 2
      (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})) := by
  apply MemLp.of_le_mul (g := u) (c := K / ε) hu
  · exact (((nativePuncturedUnitBallCutoff_contDiff ε).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable.mul hu.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cutoff_coordinate_bound ε K hK j x) (norm_nonneg _)

private theorem cutoff_error_integral_le {u : E → ℝ}
    (hu : MemLp u 2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)})))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x : E, ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ ≤ K / ε)
    (htip : MemLp u 2 (volume.restrict
      (Metric.ball (0 : E) (Real.exp (-cutoffTipTime ε)) \ {(0 : E)})))
    (hshell : MemLp u 2 (volume.restrict (cylinderShell 0 (4 * ε))))
    (j : Fin 3) :
    (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
      (fderiv ℝ (nativePuncturedUnitBallCutoff ε) x (EuclideanSpace.single j 1) * u x) ^ 2) ≤
      (K / ε) ^ 2 *
        ((∫ x in Metric.ball (0 : E) (Real.exp (-cutoffTipTime ε)) \ {(0 : E)}, u x ^ 2) +
          ∫ x in cylinderShell 0 (4 * ε), u x ^ 2) := by
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let T := Metric.ball (0 : E) (Real.exp (-cutoffTipTime ε)) \ {(0 : E)}
  let S0 := cylinderShell 0 (4 * ε)
  let A : E → ℝ := T.indicator (fun x => u x ^ 2)
  let B : E → ℝ := S0.indicator (fun x => u x ^ 2)
  have hO : MeasurableSet O := (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hT : MeasurableSet T := (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hS : MeasurableSet S0 := measurableSet_cylinderShell 0 (4 * ε)
  have hA : Integrable A := IntegrableOn.integrable_indicator htip.integrable_sq hT
  have hB : Integrable B := IntegrableOn.integrable_indicator hshell.integrable_sq hS
  have hAO : Integrable A (volume.restrict O) := hA.integrableOn
  have hBO : Integrable B (volume.restrict O) := hB.integrableOn
  have hA0 (x : E) : 0 ≤ A x := Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hB0 (x : E) : 0 ≤ B x := Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hmajor : Integrable (fun x => (K / ε) ^ 2 * (A x + B x)) (volume.restrict O) := by
    simpa only [Pi.add_apply] using (hAO.add hBO).const_mul ((K / ε) ^ 2)
  have herr := cutoff_error_memLp hu ε K hK j
  have hpoint (x : E) (hx : x ∈ O) :
      (fderiv ℝ (nativePuncturedUnitBallCutoff ε) x (EuclideanSpace.single j 1) * u x) ^ 2 ≤
        (K / ε) ^ 2 * (A x + B x) := by
    have hsq : (fderiv ℝ (nativePuncturedUnitBallCutoff ε) x
        (EuclideanSpace.single j 1)) ^ 2 ≤ (K / ε) ^ 2 := by
      have hb := cutoff_coordinate_bound ε K hK j x
      rw [Real.norm_eq_abs] at hb
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (div_nonneg hK0 hε.le)).mpr hb
    have hmul : (fderiv ℝ (nativePuncturedUnitBallCutoff ε) x
        (EuclideanSpace.single j 1) * u x) ^ 2 ≤ (K / ε) ^ 2 * u x ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    by_cases hin : ‖x‖ ^ 2 ≤ 2 * ε
    · have hxT : x ∈ T := cutoff_inner_mem_tip ε hε hx hin
      have ha : A x = u x ^ 2 := Set.indicator_of_mem hxT _
      exact hmul.trans (mul_le_mul_of_nonneg_left (by rw [ha]; linarith [hB0 x]) (sq_nonneg _))
    · by_cases hout : 1 - 2 * ε ≤ ‖x‖ ^ 2
      · have hxS : x ∈ S0 := cutoff_outer_mem_shell ε hε hε1 hx hout
        have hb : B x = u x ^ 2 := Set.indicator_of_mem hxS _
        exact hmul.trans (mul_le_mul_of_nonneg_left (by rw [hb]; linarith [hA0 x]) (sq_nonneg _))
      · have hz := nativePuncturedUnitBallCutoff_fderiv_eq_zero ε hε x
          (lt_of_not_ge hin) (lt_of_not_ge hout)
        rw [hz, ContinuousLinearMap.zero_apply, zero_mul, zero_pow (by decide : 2 ≠ 0)]
        exact mul_nonneg (sq_nonneg _) (add_nonneg (hA0 x) (hB0 x))
  have hIA : (∫ x in O, A x) ≤ ∫ x in T, u x ^ 2 := by
    calc
      _ ≤ ∫ x : E, A x := setIntegral_le_integral hA (Eventually.of_forall hA0)
      _ = _ := integral_indicator hT
  have hIB : (∫ x in O, B x) ≤ ∫ x in S0, u x ^ 2 := by
    calc
      _ ≤ ∫ x : E, B x := setIntegral_le_integral hB (Eventually.of_forall hB0)
      _ = _ := integral_indicator hS
  calc
    _ ≤ ∫ x in O, (K / ε) ^ 2 * (A x + B x) :=
      setIntegral_mono_on herr.integrable_sq hmajor hO hpoint
    _ = (K / ε) ^ 2 * ((∫ x in O, A x) + ∫ x in O, B x) := by
      rw [integral_const_mul, integral_add hAO hBO]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hIA hIB) (sq_nonneg _)

private def cutoffEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 5)

private theorem cutoffEpsilon_pos (n : ℕ) : 0 < cutoffEpsilon n := by
  dsimp only [cutoffEpsilon]
  positivity

private theorem cutoffEpsilon_le (n : ℕ) : cutoffEpsilon n ≤ 1 / 4 := by
  dsimp only [cutoffEpsilon]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 5)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

private theorem cutoffEpsilon_tendsto : Tendsto cutoffEpsilon atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 5)) atTop (𝓝 0)
  have h : Tendsto (fun n : ℕ => 1 / ((n + 5 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 5).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [cutoffEpsilon, Nat.cast_add, Nat.cast_ofNat] using h

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The actual product-rule error of the explicit smooth cutoff and
the same original forced physical function tends to zero in L2.
The cutoff scale and all error terms are literal, and no boundary trace
or approximation conclusion is an input. -/
theorem native_forced_halfEnd_cutoff_error_tendsto
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (j : Fin 3) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun x => fderiv ℝ (nativePuncturedUnitBallCutoff (1 / ((n : ℝ) + 5))) x
        (EuclideanSpace.single j 1) * cylinderLift w x)
      2 (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)}))) atTop (𝓝 0) := by
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let u := cylinderLift w
  let err : ℕ → E → ℝ := fun n x =>
    fderiv ℝ (nativePuncturedUnitBallCutoff (cutoffEpsilon n)) x
      (EuclideanSpace.single j 1) * u x
  obtain ⟨K, hK0, hK⟩ := exists_nativePuncturedUnitBallCutoff_gradient_bound
  have hu : MemLp u 2 (volume.restrict O) :=
    (native_forced_halfEnd_value_global_memLp hκ0 hκ1 V hV hV0 F hw hwAE).1
  have he (n : ℕ) : MemLp (err n) 2 (volume.restrict O) :=
    cutoff_error_memLp hu (cutoffEpsilon n) K (hK _ (cutoffEpsilon_pos n)) j
  let C0 : ℝ := 2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)
  let CD : ℝ := nativeHalfHighDirichletDerivativeBound κ V
  let M : ℝ := ((27 / 6 : ℝ) * C0 ^ 2 + (64 / 3 : ℝ) * CD ^ 2) * ‖F‖ ^ 2
  have henergy (n : ℕ) : (∫ x in O, err n x ^ 2) ≤ K ^ 2 * M * cutoffEpsilon n := by
    let ε := cutoffEpsilon n
    have hε : 0 < ε := cutoffEpsilon_pos n
    have hε1 : ε ≤ 1 / 4 := cutoffEpsilon_le n
    obtain ⟨htip, htipB⟩ := native_forced_halfEnd_value_tip_memLp
      hκ0 hκ1 V hV hV0 F hw hwAE (cutoffTipTime ε) (cutoffTipTime_nonneg ε hε hε1)
    obtain ⟨hshell, _, hshellB⟩ := native_forced_halfEnd_boundary_shell_value_sq_le
      hκ0 hκ1 V hV hV0 F hw hwAE (4 * ε) (by positivity)
    rw [cutoffTipTime_exp_six ε hε] at htipB
    have hsum :
        ((∫ x in Metric.ball (0 : E) (Real.exp (-cutoffTipTime ε)) \ {(0 : E)}, u x ^ 2) +
          ∫ x in cylinderShell 0 (4 * ε), u x ^ 2) ≤ M * ε ^ 3 := by
      calc
        _ ≤ C0 ^ 2 * ‖F‖ ^ 2 * (3 * ε) ^ 3 / 6 +
            CD ^ 2 * ‖F‖ ^ 2 * (4 * ε) ^ 3 / 3 := add_le_add htipB hshellB
        _ = _ := by dsimp only [M]; ring
    calc
      _ ≤ (K / ε) ^ 2 *
          ((∫ x in Metric.ball (0 : E) (Real.exp (-cutoffTipTime ε)) \ {(0 : E)}, u x ^ 2) +
            ∫ x in cylinderShell 0 (4 * ε), u x ^ 2) :=
        cutoff_error_integral_le hu ε hε hε1 K hK0.le (hK ε hε) htip hshell j
      _ ≤ (K / ε) ^ 2 * (M * ε ^ 3) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by
        change (K / ε) ^ 2 * (M * ε ^ 3) = K ^ 2 * M * ε
        field_simp [ne_of_gt hε] <;> ring
  have hsqLim : Tendsto (fun n => ∫ x in O, err n x ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) henergy
      (by simpa only [mul_zero] using cutoffEpsilon_tendsto.const_mul (K ^ 2 * M))
  have hz : MemLp (fun _ : E => (0 : ℝ)) 2 (volume.restrict O) := MemLp.zero'
  have hLp := native_tendsto_toLp_of_integral_sq_sub he hz
    (by simpa only [sub_zero] using hsqLim)
  have herrLim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' err he (fun _ : E => (0 : ℝ)) hz).mp hLp
  simpa only [Pi.sub_def, err, u, O, cutoffEpsilon, sub_zero] using herrLim

/-- The original constructed forced physical function belongs to the
actual zero-boundary weak Sobolev space on the punctured open unit ball.
Its global H1 witness and the actual cutoff error are both produced from
the same original forced curve and the same measurable representative. -/
theorem native_forced_halfEnd_memH01
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ)) :
    Poincare.Analysis.Sobolev.Weak.MemH01 (cylinderLift w)
      (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let χ : ℕ → E → ℝ := fun n => nativePuncturedUnitBallCutoff (cutoffEpsilon n)
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hH1 : Poincare.Analysis.Sobolev.Weak.MemH1 (cylinderLift w) O :=
    (native_forced_halfEnd_global_strong_H1 hκ0 hκ1 V hV hV0 F hw hwAE).1
  have hlim : ∀ᵐ x ∂volume.restrict O, Tendsto (fun n => χ n x) atTop (𝓝 1) := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hr1 : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
    have hs0 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hr
    have hs1 : ‖x‖ ^ 2 < 1 := by
      simpa only [one_pow] using (sq_lt_sq₀ (norm_nonneg x) zero_le_one).mpr hr1
    have hlo := cutoffEpsilon_tendsto.eventually (gt_mem_nhds (by positivity : 0 < ‖x‖ ^ 2 / 2))
    have hhi := cutoffEpsilon_tendsto.eventually
      (gt_mem_nhds (by linarith : 0 < (1 - ‖x‖ ^ 2) / 2))
    have heq : (fun n => χ n x) =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
      filter_upwards [hlo, hhi] with n hnlo hnhi
      exact nativePuncturedUnitBallCutoff_eq_one (cutoffEpsilon n) (cutoffEpsilon_pos n) x
        (by linarith) (by linarith)
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  apply native_memH01_of_smooth_cutoffs hO hH1.someWitness χ
    (fun n => nativePuncturedUnitBallCutoff_contDiff _)
    (fun n => nativePuncturedUnitBallCutoff_hasCompactSupport _ (cutoffEpsilon_pos n))
    (fun n => nativePuncturedUnitBallCutoff_tsupport_subset _ (cutoffEpsilon_pos n))
    (fun n x => nativePuncturedUnitBallCutoff_range _ x) hlim
  intro j
  exact native_forced_halfEnd_cutoff_error_tendsto hκ0 hκ1 V hV hV0 F hw hwAE j

#print axioms native_forced_halfEnd_cutoff_error_tendsto
#print axioms native_forced_halfEnd_memH01

end Yamabe3.Analysis.SpherePolar
