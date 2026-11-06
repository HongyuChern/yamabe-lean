import Yamabe3.Analysis.NativeHalfNormalRegularity
import Yamabe3.Analysis.NativeFullEntranceTraces

/-! Actual low traces have uniform three-halves/half spectral budgets.
The constants are chosen before the orbit, phase and original source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeLowProjection_three_halves_bound (f : AngularL2) :
    NativeAngularSpectralRegular (3/2) (nativeLowProjection f) ∧
      (∑' i,nativeAngularWeightedSquare (3/2) (nativeLowProjection f) i)≤8*‖f‖^2 := by
  have hs : HasSum (fun i => (inner ℝ (angularBasis i) f)^2) (‖f‖^2) := by
    have h := angularBasis.hasSum_inner_mul_inner f f
    simpa only [real_inner_comm f,←pow_two,real_inner_self_eq_norm_sq] using h
  have hb (i : AngularIndex) : nativeAngularWeightedSquare (3/2) (nativeLowProjection f) i≤
      8*(inner ℝ (angularBasis i) f)^2 := by
    rw [nativeAngularWeightedSquare_three_halves,nativeLowProjection,nativeAngularProjection_coefficient]
    split_ifs with hi
    · have heigen : angularEigenvalue i≤2 := by
        rcases angularEigenvalue_zero_two_or_ge_six i with h|h|h <;> linarith
      have hw := angularEnergyWeight_sq i
      have hp := angularEnergyWeight_pos i
      have h2 : angularEnergyWeight i≤2 := by nlinarith
      have h3 := pow_le_pow_left₀ hp.le h2 3
      exact mul_le_mul_of_nonneg_right (by norm_num at h3 ⊢;exact h3) (sq_nonneg _)
    · simp only [zero_pow (by norm_num : 2≠0),mul_zero]
      positivity
  have hmajor := hs.summable.mul_left 8
  have hr : NativeAngularSpectralRegular (3/2) (nativeLowProjection f) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hmajor
  refine ⟨hr,?_⟩
  have h := Summable.tsum_le_tsum hb hr hmajor
  simpa only [tsum_mul_left,hs.tsum_eq] using h

variable (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)

theorem nativeLowL2Normal_is_low (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeLowProjection (nativeLowL2NormalAngularCLM v hv hb F)=nativeLowL2NormalAngularCLM v hv hb F := by
  change nativeLowProjection (nativeLowProjection _)=nativeLowProjection _
  classical
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeLowProjection,nativeAngularProjection_coefficient]
  split_ifs <;> rfl

theorem nativeLowL2_true_entrance_bounds (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    ‖nativeLowL2AngularCLM v hv hb F 0‖≤4*(eLpNorm (futureL2Kernel 2) 2).toReal*‖F‖ ∧
    ‖nativeLowL2NormalAngularCLM v hv hb F‖≤22*(eLpNorm (futureL2Kernel 2) 2).toReal*‖F‖ := by
  let A := lowAngularOperatorBCF v hv hb
  let hA := lowAngularOperatorBCF_norm_le v hv hb
  have h := lowL2Entrance_bounds A hA F
  constructor
  · change ‖nativeLowProjection (angularBasis.repr.symm (lowL2EntranceCLM A hA F))‖≤_
    exact ((nativeAngularProjection_apply_norm_le _ _).trans_eq (angularBasis.repr.symm.norm_map _)).trans h.1
  · change ‖nativeLowProjection (angularBasis.repr.symm
      ((3/2:ℝ) • lowL2EntranceCLM A hA F-lowL2EntranceDerivativeCLM A hA F))‖≤_
    apply ((nativeAngularProjection_apply_norm_le _ _).trans_eq (angularBasis.repr.symm.norm_map _)).trans
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤3/2)]
    nlinarith only [h.1,h.2]

theorem nativeLowL2_true_trace_spectral_bounds (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    NativeAngularSpectralRegular (3/2) (nativeLowL2AngularCLM v hv hb F 0) ∧
    NativeAngularSpectralRegular (1/2) (nativeLowL2NormalAngularCLM v hv hb F) ∧
      (∑' i,nativeAngularWeightedSquare (3/2) (nativeLowL2AngularCLM v hv hb F 0) i)≤
        128*(eLpNorm (futureL2Kernel 2) 2).toReal^2*‖F‖^2 ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (nativeLowL2NormalAngularCLM v hv hb F) i)≤
        3872*(eLpNorm (futureL2Kernel 2) 2).toReal^2*‖F‖^2 := by
  obtain ⟨hu,hub⟩ := nativeLowProjection_three_halves_bound (nativeLowL2AngularCLM v hv hb F 0)
  rw [nativeLowL2_entrance_is_low] at hu hub
  obtain ⟨hn,hnb⟩ := nativeLowProjection_three_halves_bound (nativeLowL2NormalAngularCLM v hv hb F)
  rw [nativeLowL2Normal_is_low] at hn hnb
  obtain ⟨hn',hnb'⟩ := nativeAngular_three_halves_to_half _ hn
  have h := nativeLowL2_true_entrance_bounds v hv hb F
  have hu2 := pow_le_pow_left₀ (norm_nonneg _) h.1 2
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) h.2 2
  exact ⟨hu,hn',by nlinarith only [hub,hu2],by nlinarith only [hnb,hnb',hn2]⟩

#print axioms nativeLowProjection_three_halves_bound
#print axioms nativeLowL2Normal_is_low
#print axioms nativeLowL2_true_entrance_bounds
#print axioms nativeLowL2_true_trace_spectral_bounds
end Yamabe3.Analysis.SpherePolar
