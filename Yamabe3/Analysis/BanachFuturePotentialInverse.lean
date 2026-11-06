import Yamabe3.Analysis.BanachFutureInverse
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Aggregate future inverse for a bounded operator-valued potential

The true future Bochner integrals and a contraction in C_b(R,H) produce an
inverse before any coordinate is taken. This is the analytic low-mode
construction needed to combine all native low angular modes with the high
Hilbert inverse in one time-weighted norm.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def boundedOperatorAction (A : ℝ →ᵇ (H →L[ℝ] H)) (u : ℝ →ᵇ H) : ℝ →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => A t (u t))
    (A.continuous.clm_apply u.continuous) (‖A‖ * ‖u‖) (fun t => by
      calc
        ‖A t (u t)‖ ≤ ‖A t‖ * ‖u t‖ := (A t).le_opNorm _
        _ ≤ ‖A‖ * ‖u‖ := mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
          (norm_nonneg (u t)) (norm_nonneg A))

omit [CompleteSpace H] in
theorem boundedOperatorAction_norm_le (A : ℝ →ᵇ (H →L[ℝ] H)) (u : ℝ →ᵇ H) :
    ‖boundedOperatorAction A u‖ ≤ ‖A‖ * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm _).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg (u t)) (norm_nonneg A))

omit [CompleteSpace H] in
theorem boundedOperatorAction_sub (A : ℝ →ᵇ (H →L[ℝ] H)) (u w : ℝ →ᵇ H) :
    boundedOperatorAction A (u - w) = boundedOperatorAction A u - boundedOperatorAction A w := by
  apply BoundedContinuousFunction.ext
  intro t
  exact (A t).map_sub (u t) (w t)

def banachFuturePotentialIteration (k : ℝ) (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (F u : ℝ →ᵇ H) : ℝ →ᵇ H :=
  banachDoubleFutureResolvent k hk (F + boundedOperatorAction A u)

theorem banachFuturePotentialIteration_contracting {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H) :
    ContractingWith ⟨‖A‖ / k ^ 2, div_nonneg (norm_nonneg A) (sq_nonneg k)⟩
      (banachFuturePotentialIteration k hk A F) := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  refine ⟨(div_lt_one hk2).mpr hA, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖banachDoubleFutureResolvent k hk (F + boundedOperatorAction A u) -
    banachDoubleFutureResolvent k hk (F + boundedOperatorAction A w)‖ ≤ _
  rw [← banachDoubleFutureResolvent_sub hk]
  have he : (F + boundedOperatorAction A u) - (F + boundedOperatorAction A w) =
      boundedOperatorAction A (u - w) := by
    rw [boundedOperatorAction_sub]
    abel
  rw [he]
  change ‖banachDoubleFutureResolvent k hk (boundedOperatorAction A (u - w))‖ ≤
    (‖A‖ / k ^ 2) * ‖u - w‖
  calc
    _ ≤ ‖boundedOperatorAction A (u - w)‖ / k ^ 2 := banachDoubleFutureResolvent_norm_le hk _
    _ ≤ (‖A‖ * ‖u - w‖) / k ^ 2 :=
      div_le_div_of_nonneg_right (boundedOperatorAction_norm_le A _) hk2.le
    _ = _ := by ring

def banachFuturePotentialInverse (k : ℝ) (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H) : ℝ →ᵇ H :=
  (banachFuturePotentialIteration_contracting hk A hA F).fixedPoint
    (banachFuturePotentialIteration k hk A F)

theorem banachFuturePotentialInverse_fixed {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H) :
    banachDoubleFutureResolvent k hk
      (F + boundedOperatorAction A (banachFuturePotentialInverse k hk A hA F)) =
        banachFuturePotentialInverse k hk A hA F :=
  (banachFuturePotentialIteration_contracting hk A hA F).fixedPoint_isFixedPt

theorem banachFuturePotentialInverse_norm_le {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H) :
    ‖banachFuturePotentialInverse k hk A hA F‖ ≤ ‖F‖ / (k ^ 2 - ‖A‖) := by
  let u := banachFuturePotentialInverse k hk A hA F
  have he := banachFuturePotentialInverse_fixed hk A hA F
  have hn : ‖u‖ ≤ (‖F‖ + ‖A‖ * ‖u‖) / k ^ 2 := by
    calc
      ‖u‖ = ‖banachDoubleFutureResolvent k hk (F + boundedOperatorAction A u)‖ := congrArg norm he.symm
      _ ≤ ‖F + boundedOperatorAction A u‖ / k ^ 2 := banachDoubleFutureResolvent_norm_le hk _
      _ ≤ (‖F‖ + ‖A‖ * ‖u‖) / k ^ 2 := div_le_div_of_nonneg_right
        ((norm_add_le _ _).trans (add_le_add le_rfl (boundedOperatorAction_norm_le A u))) (sq_nonneg _)
  have hm := (le_div_iff₀ (sq_pos_of_pos hk)).mp hn
  apply (le_div_iff₀ (sub_pos.mpr hA)).mpr
  dsimp only [u] at hm ⊢
  nlinarith

/-- The same aggregate inverse satisfies its actual strong Banach equation. -/
theorem banachFuturePotentialInverse_equation {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H) :
    let u := banachFuturePotentialInverse k hk A hA F
    Differentiable ℝ (fun t => u t) ∧ Differentiable ℝ (deriv (fun t => u t)) ∧
      ∀ t, deriv (deriv (fun s => u s)) t =
        (2 * k) • deriv (fun s => u s) t - k ^ 2 • u t + F t + A t (u t) := by
  dsimp only
  let u := banachFuturePotentialInverse k hk A hA F
  have he : (fun t => banachDoubleFutureResolvent k hk (F + boundedOperatorAction A u) t) =
      fun t => u t := by
    funext t
    exact congrArg (fun w : ℝ →ᵇ H => w t) (banachFuturePotentialInverse_fixed hk A hA F)
  have h := banachDoubleFutureResolvent_equation hk (F + boundedOperatorAction A u)
  dsimp only at h
  rw [he] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have ht := h.2.2.2 t
  rw [congrFun he t] at ht
  change deriv (deriv (fun t => u t)) t =
    (2 * k) • deriv (fun t => u t) t - k ^ 2 • u t + (F t + A t (u t)) at ht
  simpa only [add_assoc] using ht

/-- An annihilated continuous linear observable remains zero under each
actual future integral. This will preserve the native high-mode complement
of the low-mode solve without summing coordinate suprema. -/
theorem banachFutureResolvent_observable_zero {k : ℝ} (hk : 0 < k)
    (F : ℝ →ᵇ H) (L : H →L[ℝ] ℝ) (hF : ∀ t, L (F t) = 0) (t : ℝ) :
    L (banachFutureResolvent k hk F t) = 0 := by
  change L (Real.exp (k * t) • ∫ s in Ioi t, Real.exp (-k * s) • F s) = 0
  rw [map_smul, ← L.integral_comp_comm (banachFutureTail_integrable hk F t)]
  simp only [map_smul, hF, smul_zero, integral_zero]

theorem banachDoubleFutureResolvent_observable_zero {k : ℝ} (hk : 0 < k)
    (F : ℝ →ᵇ H) (L : H →L[ℝ] ℝ) (hF : ∀ t, L (F t) = 0) (t : ℝ) :
    L (banachDoubleFutureResolvent k hk F t) = 0 :=
  banachFutureResolvent_observable_zero hk _ L
    (banachFutureResolvent_observable_zero hk F L hF) t

/-- A linear invariant of the actual source and potential is preserved by
all Banach iterates and their norm limit. -/
theorem banachFuturePotentialInverse_observable_zero {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H)
    (L : H →L[ℝ] ℝ) (hF : ∀ t, L (F t) = 0)
    (hAL : ∀ t x, L x = 0 → L (A t x) = 0) :
    ∀ t, L (banachFuturePotentialInverse k hk A hA F t) = 0 := by
  let T := banachFuturePotentialIteration k hk A F
  have hc := banachFuturePotentialIteration_contracting hk A hA F
  have hz (n : ℕ) : ∀ t, L ((T^[n] 0) t) = 0 := by
    induction n with
    | zero => intro t; exact map_zero L
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply']
      apply banachDoubleFutureResolvent_observable_zero hk _ L
      intro s
      change L (F s + A s ((T^[n] 0) s)) = 0
      rw [map_add, hF, hAL s _ (ih s), add_zero]
  intro t
  have hev : Continuous (fun w : ℝ →ᵇ H => L (w t)) :=
    L.continuous.comp (BoundedContinuousFunction.evalCLM ℝ t).continuous
  have hlim := hev.continuousAt.tendsto.comp (hc.tendsto_iterate_fixedPoint 0)
  have hzlim : Tendsto (fun n : ℕ => L ((T^[n] 0) t)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hzlim

end Yamabe3.Analysis.Delaunay
