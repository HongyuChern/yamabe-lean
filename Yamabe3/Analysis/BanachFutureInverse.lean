import Yamabe3.Analysis.ExponentialFutureInverse

/-!
# Genuine future inverses in a complete Banach space

The actual future Bochner integral is differentiated by reducing its moving
half-line to an interval primitive. Its aggregate norm is controlled before
taking any coordinate. Composing two such tails yields a genuine strong
Banach-valued inverse of (D-k)^2, used for the full low angular subspace.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def banachFutureTail (k : ℝ) (F : ℝ → H) (t : ℝ) : H :=
  Real.exp (k * t) • ∫ s in Ioi t, Real.exp (-k * s) • F s

omit [CompleteSpace H] in
theorem banachFutureTail_integrable {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ H) (t : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-k * s) • F s) (Ioi t) := by
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hk) t).const_mul ‖F‖).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul F.continuous).aestronglyMeasurable.restrict
  exact Eventually.of_forall fun s => by
    change ‖Real.exp (-k * s) • F s‖ ≤ ‖F‖ * Real.exp (-k * s)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm s) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

omit [CompleteSpace H] in
theorem banachFutureTail_bound {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ H) (t : ℝ) :
    ‖banachFutureTail k F t‖ ≤ ‖F‖ / k := by
  have hm := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hk) t).const_mul ‖F‖
  have h := norm_integral_le_of_norm_le
    (f := fun s : ℝ => Real.exp (-k * s) • F s) hm
    (Eventually.of_forall fun s => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm s) (Real.exp_pos _).le).trans_eq (mul_comm _ _))
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hk)] at h
  have he : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
    rw [← Real.exp_add, show k * t + -k * t = 0 by ring, Real.exp_zero]
  rw [banachFutureTail, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (k * t) * (‖F‖ * (-Real.exp (-k * t) / -k)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      calc
        _ = (‖F‖ / k) * (Real.exp (k * t) * Real.exp (-k * t)) := by ring
        _ = _ := by rw [he, mul_one]

theorem banachFutureTail_hasDerivAt {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ H) (t : ℝ) :
    HasDerivAt (banachFutureTail k F) (k • banachFutureTail k F t - F t) t := by
  let G : ℝ → H := fun s => Real.exp (-k * s) • F s
  have hG : Continuous G :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul F.continuous
  have heq : (fun y : ℝ => ∫ s in Ioi y, G s) =
      fun y => (∫ s in Ioi (0 : ℝ), G s) - ∫ s in (0 : ℝ)..y, G s := by
    funext y
    have h := intervalIntegral.integral_Ioi_sub_Ioi'
      (banachFutureTail_integrable hk F 0) (banachFutureTail_integrable hk F y)
    apply eq_sub_iff_add_eq.mpr
    rw [← h]
    abel
  have hd : HasDerivAt (fun y : ℝ => ∫ s in Ioi y, G s) (-(G t)) t := by
    rw [heq]
    exact (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable _ _)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_sub _
  have hx : HasDerivAt (fun y : ℝ => Real.exp (k * y)) (k * Real.exp (k * t)) t := by
    apply (((hasDerivAt_id t).const_mul k).exp).congr_deriv
    simp only [id_eq]
    ring
  apply (hx.smul hd).congr_deriv
  have hexp : Real.exp (k * t) * Real.exp (-k * t) = 1 := by
    rw [← Real.exp_add, show k * t + -k * t = 0 by ring, Real.exp_zero]
  dsimp only [G, banachFutureTail]
  rw [smul_neg, smul_smul, hexp, one_smul, smul_smul]
  abel

def banachFutureResolvent (k : ℝ) (hk : 0 < k) (F : ℝ →ᵇ H) : ℝ →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroup (banachFutureTail k F)
    (continuous_iff_continuousAt.mpr fun t => (banachFutureTail_hasDerivAt hk F t).continuousAt)
    (‖F‖ / k) (banachFutureTail_bound hk F)

theorem banachFutureResolvent_norm_le {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ H) :
    ‖banachFutureResolvent k hk F‖ ≤ ‖F‖ / k :=
  (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg F) hk.le)).mpr
    (banachFutureTail_bound hk F)

theorem banachFutureResolvent_sub {k : ℝ} (hk : 0 < k) (F G : ℝ →ᵇ H) :
    banachFutureResolvent k hk (F - G) = banachFutureResolvent k hk F - banachFutureResolvent k hk G := by
  apply BoundedContinuousFunction.ext
  intro t
  change banachFutureTail k (fun s => F s - G s) t = banachFutureTail k F t - banachFutureTail k G t
  unfold banachFutureTail
  simp_rw [smul_sub]
  rw [integral_sub (banachFutureTail_integrable hk F t) (banachFutureTail_integrable hk G t), smul_sub]

def banachDoubleFutureResolvent (k : ℝ) (hk : 0 < k) (F : ℝ →ᵇ H) : ℝ →ᵇ H :=
  banachFutureResolvent k hk (banachFutureResolvent k hk F)

theorem banachDoubleFutureResolvent_norm_le {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ H) :
    ‖banachDoubleFutureResolvent k hk F‖ ≤ ‖F‖ / k ^ 2 := by
  calc
    _ ≤ ‖banachFutureResolvent k hk F‖ / k := banachFutureResolvent_norm_le hk _
    _ ≤ (‖F‖ / k) / k := div_le_div_of_nonneg_right (banachFutureResolvent_norm_le hk F) hk.le
    _ = _ := by ring

theorem banachDoubleFutureResolvent_sub {k : ℝ} (hk : 0 < k) (F G : ℝ →ᵇ H) :
    banachDoubleFutureResolvent k hk (F - G) =
      banachDoubleFutureResolvent k hk F - banachDoubleFutureResolvent k hk G := by
  unfold banachDoubleFutureResolvent
  rw [banachFutureResolvent_sub hk, banachFutureResolvent_sub hk]

/-- The actual strong Banach-valued second-order equation of the two
future tails. There is no interchange of a mode sum and a time supremum. -/
theorem banachDoubleFutureResolvent_equation {k : ℝ} (hk : 0 < k) (F : ℝ →ᵇ H) :
    let u := fun t => banachDoubleFutureResolvent k hk F t
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      (∀ t, deriv u t = k • u t - banachFutureResolvent k hk F t) ∧
      ∀ t, deriv (deriv u) t = (2 * k) • deriv u t - k ^ 2 • u t + F t := by
  dsimp only
  have hd (t : ℝ) := banachFutureTail_hasDerivAt hk (banachFutureResolvent k hk F) t
  have heq : deriv (fun t => banachDoubleFutureResolvent k hk F t) =
      fun t => k • banachDoubleFutureResolvent k hk F t - banachFutureResolvent k hk F t :=
    funext fun t => (hd t).deriv
  have hd2 (t : ℝ) : HasDerivAt
      (fun s => k • banachDoubleFutureResolvent k hk F s - banachFutureResolvent k hk F s)
      (k • (k • banachDoubleFutureResolvent k hk F t - banachFutureResolvent k hk F t) -
        (k • banachFutureResolvent k hk F t - F t)) t :=
    ((hd t).const_smul k).sub (banachFutureTail_hasDerivAt hk F t)
  refine ⟨fun t => (hd t).differentiableAt, ?_, fun t => (hd t).deriv, ?_⟩
  · rw [heq]
    exact fun t => (hd2 t).differentiableAt
  · intro t
    rw [heq, (hd2 t).deriv]
    module

end Yamabe3.Analysis.Delaunay
