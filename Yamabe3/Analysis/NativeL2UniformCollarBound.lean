import Yamabe3.Analysis.NativeL2ParticularExtension

/-! The same physical H2 collar estimate is uniform over all potentials
with the original two kernel bounds and one fixed sup norm bound. Constants
precede the potential and source, so translations cannot change them. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem sqrt_bound {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0≤C) (h : ‖y‖^2≤C*‖x‖^2) : ‖y‖≤Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0≤Real.sqrt C*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg y]

 theorem exists_uniform_nativeL2Particular_collar_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀ k,0≤K k) ∧
      ∀ (V : ℝ →ᵇ ℝ),‖V‖≤M →
      ∀ (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
        (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
        (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)),
      ‖nativeL2ParticularValueCLM hκ0 hκ1 V hminus hplus F‖≤C*‖F‖ ∧
      (∀ j,‖nativeL2ParticularFirstCLM hκ0 hκ1 V hminus hplus j F‖≤G*‖F‖) ∧
      (∀ k j,‖nativeL2ParticularSecondCLM hκ0 hκ1 V hminus hplus k j F‖≤K k*‖F‖) := by
  obtain ⟨G,K,hG,hK,he⟩ := exists_nativeC2Collar_series_norm_bounds (ι := AngularIndex)
  let B := (1-κ)⁻¹*(4/9:ℝ)
  let C := Real.exp 6*B^2+Real.exp 2*(1+M*B)^2
  have hB : 0≤B := by dsimp only [B];positivity
  have hC : 0≤C := by dsimp only [C];positivity
  refine ⟨Real.sqrt C,Real.sqrt (G*C),fun k => Real.sqrt (K k*C),Real.sqrt_nonneg _,Real.sqrt_nonneg _,
    fun k => Real.sqrt_nonneg _,fun V hVM hminus hplus F => ?_⟩
  have hb (H : continuousL2Source (SpectralSpace AngularIndex)) :
      ‖nativeL2ParticularValueLinear hκ0 hκ1 V hminus hplus H‖≤Real.sqrt C*‖continuousL2SourceInclusion _ H‖ ∧
      (∀ j,‖nativeL2ParticularFirstLinear hκ0 hκ1 V hminus hplus j H‖≤Real.sqrt (G*C)*‖continuousL2SourceInclusion _ H‖) ∧
      (∀ k j,‖nativeL2ParticularSecondLinear hκ0 hκ1 V hminus hplus k j H‖≤Real.sqrt (K k*C)*‖continuousL2SourceInclusion _ H‖) := by
    have hh := he _ (nativeL2ParticularMode_C2 hκ0 hκ1 V hminus hplus H.val H.property) _
      (nativeL2ParticularModeBudget_summable hκ0 hκ1 V hminus hplus H.val H.property)
      (nativeL2ParticularModeBudget_nonneg hκ0 hκ1 V hminus H.val) 1 (by norm_num)
      (by intro s;simpa only [one_mul] using nativeL2ParticularMode_finite_budget hκ0 hκ1 V hminus hplus H.val H.property s)
    simp only [one_mul,mul_one] at hh
    have hbudget := nativeL2ParticularModeBudget_total_le hκ0 hκ1 V hminus hplus H.val H.property
    have hCV : Real.exp 6*B^2+Real.exp 2*(1+‖V‖*B)^2≤C := by
      dsimp only [C]
      gcongr
    have hbtotal : (∑' i,nativeL2ParticularModeBudget hκ0 hκ1 V hminus H.val i)≤C*‖continuousL2SourceInclusion _ H‖^2 :=
      hbudget.trans (mul_le_mul_of_nonneg_right hCV (sq_nonneg _))
    refine ⟨sqrt_bound _ _ hC (hh.1.trans hbtotal),fun j => ?_,fun k j => ?_⟩
    · apply sqrt_bound _ _ (mul_nonneg hG hC)
      exact (hh.2.1 j).trans ((mul_le_mul_of_nonneg_left hbtotal hG).trans_eq (by ring))
    · apply sqrt_bound _ _ (mul_nonneg (hK k) hC)
      exact (hh.2.2 k j).trans ((mul_le_mul_of_nonneg_left hbtotal (hK k)).trans_eq (by ring))
  exact ⟨LinearMap.norm_extendOfNorm_apply_le (continuousL2SourceInclusion_dense _) _ (fun H => (hb H).1) F,
    fun j => LinearMap.norm_extendOfNorm_apply_le (continuousL2SourceInclusion_dense _) _ (fun H => (hb H).2.1 j) F,
    fun k j => LinearMap.norm_extendOfNorm_apply_le (continuousL2SourceInclusion_dense _) _ (fun H => (hb H).2.2 k j) F⟩

#print axioms exists_uniform_nativeL2Particular_collar_bounds
end Yamabe3.Analysis.SpherePolar
