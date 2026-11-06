import Yamabe3.Analysis.BanachFuturePotentialInverse

/-!
# Linearity of the genuine aggregate future inverse

The two future Bochner integrals are linear. Uniqueness of the actual
operator-valued-potential fixed point therefore gives linearity of the
same constructed inverse, including its quantitative source-difference
bound on the complete bounded-continuous Banach space.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem banachFutureResolvent_add {k : ℝ} (hk : 0 < k) (F G : ℝ →ᵇ H) :
    banachFutureResolvent k hk (F + G) = banachFutureResolvent k hk F + banachFutureResolvent k hk G := by
  have h := banachFutureResolvent_sub hk (F + G) G
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm

theorem banachFutureResolvent_smul {k : ℝ} (hk : 0 < k) (c : ℝ) (F : ℝ →ᵇ H) :
    banachFutureResolvent k hk (c • F) = c • banachFutureResolvent k hk F := by
  apply BoundedContinuousFunction.ext
  intro t
  change Real.exp (k * t) • (∫ s in Ioi t, Real.exp (-k * s) • (c • F s)) =
    c • (Real.exp (k * t) • ∫ s in Ioi t, Real.exp (-k * s) • F s)
  simp_rw [smul_comm (Real.exp (-k * _)) c, integral_smul]
  exact smul_comm _ _ _

theorem banachDoubleFutureResolvent_add {k : ℝ} (hk : 0 < k) (F G : ℝ →ᵇ H) :
    banachDoubleFutureResolvent k hk (F + G) =
      banachDoubleFutureResolvent k hk F + banachDoubleFutureResolvent k hk G := by
  unfold banachDoubleFutureResolvent
  rw [banachFutureResolvent_add hk, banachFutureResolvent_add hk]

theorem banachDoubleFutureResolvent_smul {k : ℝ} (hk : 0 < k) (c : ℝ) (F : ℝ →ᵇ H) :
    banachDoubleFutureResolvent k hk (c • F) = c • banachDoubleFutureResolvent k hk F := by
  unfold banachDoubleFutureResolvent
  rw [banachFutureResolvent_smul hk, banachFutureResolvent_smul hk]

omit [CompleteSpace H] in
theorem boundedOperatorAction_add (A : ℝ →ᵇ (H →L[ℝ] H)) (u w : ℝ →ᵇ H) :
    boundedOperatorAction A (u + w) = boundedOperatorAction A u + boundedOperatorAction A w := by
  apply BoundedContinuousFunction.ext
  intro t
  exact (A t).map_add (u t) (w t)

omit [CompleteSpace H] in
theorem boundedOperatorAction_smul (A : ℝ →ᵇ (H →L[ℝ] H)) (c : ℝ) (u : ℝ →ᵇ H) :
    boundedOperatorAction A (c • u) = c • boundedOperatorAction A u := by
  apply BoundedContinuousFunction.ext
  intro t
  exact (A t).map_smul c (u t)

theorem banachFuturePotentialInverse_add {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F G : ℝ →ᵇ H) :
    banachFuturePotentialInverse k hk A hA (F + G) =
      banachFuturePotentialInverse k hk A hA F + banachFuturePotentialInverse k hk A hA G := by
  let u := banachFuturePotentialInverse k hk A hA F
  let w := banachFuturePotentialInverse k hk A hA G
  have hfixed : Function.IsFixedPt (banachFuturePotentialIteration k hk A (F + G)) (u + w) := by
    change banachDoubleFutureResolvent k hk ((F + G) + boundedOperatorAction A (u + w)) = u + w
    rw [boundedOperatorAction_add]
    have he : F + G + (boundedOperatorAction A u + boundedOperatorAction A w) =
        (F + boundedOperatorAction A u) + (G + boundedOperatorAction A w) := by abel
    rw [he, banachDoubleFutureResolvent_add hk,
      banachFuturePotentialInverse_fixed hk A hA F, banachFuturePotentialInverse_fixed hk A hA G]
  exact ((banachFuturePotentialIteration_contracting hk A hA (F + G)).fixedPoint_unique hfixed).symm

theorem banachFuturePotentialInverse_smul {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (c : ℝ) (F : ℝ →ᵇ H) :
    banachFuturePotentialInverse k hk A hA (c • F) = c • banachFuturePotentialInverse k hk A hA F := by
  let u := banachFuturePotentialInverse k hk A hA F
  have hfixed : Function.IsFixedPt (banachFuturePotentialIteration k hk A (c • F)) (c • u) := by
    change banachDoubleFutureResolvent k hk (c • F + boundedOperatorAction A (c • u)) = c • u
    rw [boundedOperatorAction_smul, ← smul_add, banachDoubleFutureResolvent_smul hk,
      banachFuturePotentialInverse_fixed hk A hA F]
  exact ((banachFuturePotentialIteration_contracting hk A hA (c • F)).fixedPoint_unique hfixed).symm

def banachFuturePotentialInverseCLM (k : ℝ) (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) : (ℝ →ᵇ H) →L[ℝ] (ℝ →ᵇ H) :=
  ({ toFun := banachFuturePotentialInverse k hk A hA
     map_add' := banachFuturePotentialInverse_add hk A hA
     map_smul' := banachFuturePotentialInverse_smul hk A hA } :
    (ℝ →ᵇ H) →ₗ[ℝ] (ℝ →ᵇ H)).mkContinuous (k ^ 2 - ‖A‖)⁻¹ (fun F => by
      change ‖banachFuturePotentialInverse k hk A hA F‖ ≤ _
      simpa only [div_eq_mul_inv, mul_comm ‖F‖] using banachFuturePotentialInverse_norm_le hk A hA F)

theorem banachFuturePotentialInverseCLM_norm_le {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) :
    ‖banachFuturePotentialInverseCLM k hk A hA‖ ≤ (k ^ 2 - ‖A‖)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (sub_pos.mpr hA).le)
  intro F
  change ‖banachFuturePotentialInverse k hk A hA F‖ ≤ _
  simpa only [div_eq_mul_inv, mul_comm ‖F‖] using banachFuturePotentialInverse_norm_le hk A hA F

end Yamabe3.Analysis.Delaunay
