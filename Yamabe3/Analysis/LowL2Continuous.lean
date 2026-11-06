import Yamabe3.Analysis.FutureL2Smoothing

/-! One canonical C1 representative and actual bounded entrance value and
derivative for the same low L2 inverse. Entrance values are constructed,
not imposed or selected from an arbitrary L2 representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def lowL2EffectiveSourceCLM (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] Lp H 2 (volume : Measure ℝ) :=
  ContinuousLinearMap.id ℝ _+(l2BoundedOperatorActionCLM A).comp (lowL2FutureInverseCLM A hA)

theorem lowL2EffectiveSource_norm (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) : ‖lowL2EffectiveSourceCLM A hA F‖≤8*‖F‖ := by
  have hR := (lowL2FutureInverseCLM A hA).le_of_opNorm_le (lowL2FutureInverse_norm A hA) F
  have hM := (l2BoundedOperatorActionCLM A).le_of_opNorm_le ((l2BoundedOperatorActionCLM_norm A).trans hA)
    (lowL2FutureInverseCLM A hA F)
  change ‖F+l2BoundedOperatorActionCLM A (lowL2FutureInverseCLM A hA F)‖≤_
  apply (norm_add_le _ _).trans
  nlinarith

def lowL2ContinuousCLM (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ H) :=
  (doubleFutureL2SmoothingCLM 2 (by norm_num)).comp (lowL2EffectiveSourceCLM A hA)

def lowL2DerivativeCLM (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] (ℝ →ᵇ H) :=
  (2:ℝ) • lowL2ContinuousCLM A hA-
    (futureL2SmoothingCLM 2 (by norm_num)).comp (lowL2EffectiveSourceCLM A hA)

def lowL2EntranceCLM (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] H :=
  (BoundedContinuousFunction.evalCLM ℝ 0).comp (lowL2ContinuousCLM A hA)

def lowL2EntranceDerivativeCLM (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    Lp H 2 (volume : Measure ℝ) →L[ℝ] H :=
  (BoundedContinuousFunction.evalCLM ℝ 0).comp (lowL2DerivativeCLM A hA)

theorem lowL2Continuous_ae (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    (lowL2ContinuousCLM A hA F : ℝ → H)=ᵐ[volume](lowL2FutureInverseCLM A hA F : ℝ → H) := by
  have h := doubleFutureL2Smoothing_ae (by norm_num : (0:ℝ)<2) (lowL2EffectiveSourceCLM A hA F)
  change (lowL2ContinuousCLM A hA F : ℝ → H)=ᵐ[volume]
    (doubleFutureL2CLM 2 (by norm_num) (F+l2BoundedOperatorActionCLM A (lowL2FutureInverseCLM A hA F)) : ℝ → H) at h
  rwa [lowL2FutureInverse_fixed] at h

theorem lowL2Continuous_hasDerivAt (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) (t : ℝ) :
    HasDerivAt (fun s => lowL2ContinuousCLM A hA F s) (lowL2DerivativeCLM A hA F t) t :=
  doubleFutureL2Smoothing_hasDerivAt (by norm_num : (0:ℝ)<2) (lowL2EffectiveSourceCLM A hA F) t

theorem lowL2Continuous_norm (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    ‖lowL2ContinuousCLM A hA F‖≤(4*(eLpNorm (futureL2Kernel 2) 2).toReal)*‖F‖ := by
  have h := doubleFutureL2Smoothing_norm (by norm_num : (0:ℝ)<2) (lowL2EffectiveSourceCLM A hA F)
  apply h.trans
  exact (mul_le_mul_of_nonneg_left (lowL2EffectiveSource_norm A hA F) (by positivity)).trans_eq (by ring)

theorem lowL2Derivative_operatorNorm (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2) :
    ‖lowL2DerivativeCLM A hA‖ ≤ 16*(eLpNorm (futureL2Kernel 2) 2).toReal := by
  let K := (eLpNorm (futureL2Kernel 2) 2).toReal
  have hU : ‖lowL2ContinuousCLM A hA‖ ≤ 4*K :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (lowL2Continuous_norm A hA)
  have hS : ‖futureL2SmoothingCLM (H := H) 2 (by norm_num)‖ ≤ K :=
    ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg (futureL2Smoothing_norm (by norm_num))
  have hG : ‖lowL2EffectiveSourceCLM A hA‖ ≤ 8 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (lowL2EffectiveSource_norm A hA)
  unfold lowL2DerivativeCLM
  calc
    _ ≤ ‖(2:ℝ) • lowL2ContinuousCLM A hA‖+
        ‖(futureL2SmoothingCLM 2 (by norm_num)).comp (lowL2EffectiveSourceCLM A hA)‖ := norm_sub_le _ _
    _ ≤ 2*‖lowL2ContinuousCLM A hA‖+‖futureL2SmoothingCLM (H := H) 2 (by norm_num)‖*‖lowL2EffectiveSourceCLM A hA‖ := by
      rw [norm_smul,Real.norm_ofNat]
      exact add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le (futureL2SmoothingCLM (H := H) 2 (by norm_num)) (lowL2EffectiveSourceCLM A hA))
    _ ≤ 2*(4*K)+K*8 := add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num))
      (mul_le_mul hS hG (norm_nonneg _) ENNReal.toReal_nonneg)
    _ = _ := by dsimp only [K];ring

theorem lowL2Derivative_norm (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    ‖lowL2DerivativeCLM A hA F‖≤(16*(eLpNorm (futureL2Kernel 2) 2).toReal)*‖F‖ :=
  (lowL2DerivativeCLM A hA).le_of_opNorm_le (lowL2Derivative_operatorNorm A hA) F

theorem lowL2Entrance_bounds (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖≤7/2)
    (F : Lp H 2 (volume : Measure ℝ)) :
    ‖lowL2EntranceCLM A hA F‖≤(4*(eLpNorm (futureL2Kernel 2) 2).toReal)*‖F‖ ∧
    ‖lowL2EntranceDerivativeCLM A hA F‖≤(16*(eLpNorm (futureL2Kernel 2) 2).toReal)*‖F‖ :=
  ⟨((lowL2ContinuousCLM A hA F).norm_coe_le_norm 0).trans (lowL2Continuous_norm A hA F),
    ((lowL2DerivativeCLM A hA F).norm_coe_le_norm 0).trans (lowL2Derivative_norm A hA F)⟩

#print axioms lowL2EffectiveSource_norm
#print axioms lowL2Continuous_ae
#print axioms lowL2Continuous_hasDerivAt
#print axioms lowL2Continuous_norm
#print axioms lowL2Derivative_operatorNorm
#print axioms lowL2Derivative_norm
#print axioms lowL2Entrance_bounds
end Yamabe3.Analysis.Delaunay
