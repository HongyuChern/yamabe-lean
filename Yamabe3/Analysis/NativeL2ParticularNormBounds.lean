import Yamabe3.Analysis.NativeL2ParticularH2Collar
import Yamabe3.Analysis.NativeC2CollarSeriesNorm

/-! Actual source-uniform H2 collar norms of the same continuous L2
particular solution. The norm is that of the original L2 source; constants
precede the source and finite-mode limits. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

include hplus in
theorem nativeL2ParticularModeBudget_total_le
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2) :
    (∑' i,nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i)≤
      (Real.exp 6*((1-κ)⁻¹*(4/9))^2+Real.exp 2*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2)*‖hF.toLp F‖^2 := by
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num : (0:ℝ)<5/2)
    nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F
  let G := fun t => F t-V t • U t
  obtain ⟨hU,hG,hUn,hGn⟩ := spectralIntegralPotentialInverse_actual_square_bounds nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa only [neg_neg] using hplus) F hF
  apply Real.tsum_le_of_sum_le (nativeL2ParticularModeBudget_nonneg hκ0 hκ1 V hminus F)
  intro s
  have hs : (∑ i ∈ s,nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i)=
      Real.exp 6*(∑ i ∈ s,∫ t : ℝ,(U t i)^2)+Real.exp 2*(∑ i ∈ s,∫ t : ℝ,(G t i)^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    rfl
  rw [hs]
  have hu := (spectralL2_finite_coordinate_integral_bound U hU s).trans hUn
  have hg := (spectralL2_finite_coordinate_integral_bound G hG s).trans hGn
  have hb := add_le_add (mul_le_mul_of_nonneg_left hu (Real.exp_pos 6).le)
    (mul_le_mul_of_nonneg_left hg (Real.exp_pos 2).le)
  exact hb.trans_eq (by norm_num;ring)

theorem exists_nativeL2Particular_H2_norm_bounds :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀ k,0≤K k) ∧
      ∀ (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2),
      ‖nativeL2ParticularCollarValue hκ0 hκ1 V hminus hplus F hF‖^2≤C*‖hF.toLp F‖^2 ∧
      (∀ j,‖nativeL2ParticularCollarFirst hκ0 hκ1 V hminus hplus F hF j‖^2≤G*‖hF.toLp F‖^2) ∧
      (∀ k j,‖nativeL2ParticularCollarSecond hκ0 hκ1 V hminus hplus F hF k j‖^2≤K k*‖hF.toLp F‖^2) := by
  obtain ⟨G,K,hG,hK,he⟩ := exists_nativeC2Collar_series_norm_bounds (ι := AngularIndex)
  let C := Real.exp 6*((1-κ)⁻¹*(4/9))^2+Real.exp 2*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨C,G*C,fun k => K k*C,hC,mul_nonneg hG hC,fun k => mul_nonneg (hK k) hC,?_⟩
  intro F hF
  have hh := he _ (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus F hF) _
    (nativeL2ParticularModeBudget_summable hκ0 hκ1 V hminus hplus F hF)
    (nativeL2ParticularModeBudget_nonneg hκ0 hκ1 V hminus F) 1 (by norm_num)
    (by intro s;simpa only [one_mul] using nativeL2ParticularMode_finite_budget hκ0 hκ1 V hminus hplus F hF s)
  simp only [one_mul,mul_one] at hh
  have hb := nativeL2ParticularModeBudget_total_le hκ0 hκ1 V hminus hplus F hF
  refine ⟨hh.1.trans hb,fun j => ?_,fun k j => ?_⟩
  · exact (hh.2.1 j).trans ((mul_le_mul_of_nonneg_left hb hG).trans_eq (by ring))
  · exact (hh.2.2 k j).trans ((mul_le_mul_of_nonneg_left hb (hK k)).trans_eq (by ring))

#print axioms nativeL2ParticularModeBudget_total_le
#print axioms exists_nativeL2Particular_H2_norm_bounds
end Yamabe3.Analysis.SpherePolar
