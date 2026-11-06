import Yamabe3.Analysis.NativeFamilyEntranceBounds

/-! Constants chosen before the potential, for the original solver and
entrance correction. No new field or boundary condition is substituted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
private theorem sqrt_bound {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0 ≤ C) (h : ‖y‖^2 ≤ C*‖x‖^2) : ‖y‖ ≤ Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0 ≤ Real.sqrt C*‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg y]

 theorem exists_family_nativePoissonTail_H2_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ),
      ∀ (s : ℝ),1 ≤ s → ∀ b : AngularH1,
        ‖nativePoissonTailValue P hplus s b‖ ≤ C*‖b‖ ∧
        (∀ j,‖nativePoissonTailFirst P hplus s b j‖ ≤ G*‖b‖) ∧
        (∀ k j,‖nativePoissonTailSecond P hplus s b k j‖ ≤ K k*‖b‖) := by
  obtain ⟨G,K,hG,hK,hfree⟩ := exists_uniform_nativeFreeTail_H2_bounds
  obtain ⟨C0,C1,C2,hC0,hC1,hC2,hcorr⟩ := exists_family_nativeL2_shifted_collar_bounds hκ0 hκ1 hM
  obtain ⟨B,hB,hb⟩ := exists_family_nativePoissonL2CorrectionSource_bound hM
  refine ⟨Real.sqrt (2*Real.exp 6)+C0*B,Real.sqrt G+C1*B,fun k => Real.sqrt (K k)+C2 k*B,
    by positivity,by positivity,fun k => add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hC2 k) hB),?_⟩
  intro P hP hPM hplus s hs b
  have hb := hb P hPM
  have hf := hfree s hs (nativePoissonAuxiliary P b)
  have hc := hcorr P hP hPM hplus (nativePoissonL2CorrectionSource P b) s
  have hF0 := (sqrt_bound _ _ (by positivity) hf.1).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) (Real.sqrt_nonneg _))
  have hF1 (j : Fin 3) := (sqrt_bound _ _ hG (hf.2.1 j)).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) (Real.sqrt_nonneg _))
  have hF2 (k j : Fin 3) := (sqrt_bound _ _ (hK k) (hf.2.2 k j)).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) (Real.sqrt_nonneg _))
  refine ⟨?_,fun j => ?_,fun k j => ?_⟩
  · exact (norm_sub_le _ _).trans ((add_le_add hF0
      (hc.1.trans (mul_le_mul_of_nonneg_left (hb b) hC0))).trans_eq (by ring))
  · exact (norm_sub_le _ _).trans ((add_le_add (hF1 j)
      ((hc.2.1 j).trans (mul_le_mul_of_nonneg_left (hb b) hC1))).trans_eq (by ring))
  · exact (norm_sub_le _ _).trans ((add_le_add (hF2 k j)
      ((hc.2.2 k j).trans (mul_le_mul_of_nonneg_left (hb b) (hC2 k)))).trans_eq (by ring))

#print axioms exists_family_nativePoissonTail_H2_bounds
end Yamabe3.Analysis.SpherePolar
