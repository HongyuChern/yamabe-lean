import Yamabe3.Analysis.NativeFamilyPoissonAllScale
import Yamabe3.Analysis.NativeL2HalfAllScaleH2

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

 theorem exists_family_nativeL2HalfAllScale_H2_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0 ≤ C ∧ 0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ),
      ∀ (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (s : ℝ),
        ‖nativeL2HalfAllScaleValue P hplus s F‖ ≤ C*‖F‖ ∧
        (∀ j,‖nativeL2HalfAllScaleFirst P hplus s F j‖ ≤ G*‖F‖) ∧
        (∀ k j,‖nativeL2HalfAllScaleSecond P hplus s F k j‖ ≤ K k*‖F‖) := by
  obtain ⟨C,G,K,hC,hG,hK,hpart⟩ := exists_family_nativeL2_shifted_collar_bounds hκ0 hκ1 hM
  obtain ⟨D,H,L,hD,hH,hL,hpoisson⟩ := exists_family_nativePoissonAllScale_H2_bounds hκ0 hκ1 hM
  let B := 2*((50/9)*(1+M*((1-κ)⁻¹*(4/9)))^2)
  have hB : 0 ≤ B := by dsimp [B];positivity
  refine ⟨C+Real.sqrt (D*B),G+Real.sqrt (H*B),fun k => K k+Real.sqrt (L k*B),
    by positivity,by positivity,fun k => add_nonneg (hK k) (Real.sqrt_nonneg _),?_⟩
  intro P hP hPM hplus F s
  have hpart := hpart P hP hPM hplus
  have hpoisson := hpoisson P hP hPM hplus
  have hp := hpart F s
  have hz := hpoisson (nativeL2HalfEntrance P hplus F)
    (nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F).2.1 s
  have hb : nativePoissonBoundaryEnergy (nativeL2HalfEntrance P hplus F)≤B*‖F‖^2 := by
    apply (nativeL2HalfEntrance_boundary_energy_bound P hplus F).trans
    rw [hP]
    dsimp only [B]
    gcongr
  have h0 := sqrt_bound F _ (mul_nonneg hD hB)
    (hz.1.trans ((mul_le_mul_of_nonneg_left hb hD).trans_eq (by ring)))
  have h1 (j : Fin 3) := sqrt_bound F _ (mul_nonneg hH hB)
    ((hz.2.1 j).trans ((mul_le_mul_of_nonneg_left hb hH).trans_eq (by ring)))
  have h2 (k j : Fin 3) := sqrt_bound F _ (mul_nonneg (hL k) hB)
    ((hz.2.2 k j).trans ((mul_le_mul_of_nonneg_left hb (hL k)).trans_eq (by ring)))
  exact ⟨(norm_sub_le _ _).trans ((add_le_add hp.1 h0).trans_eq (by ring)),
    fun j => (norm_sub_le _ _).trans ((add_le_add (hp.2.1 j) (h1 j)).trans_eq (by ring)),
    fun k j => (norm_sub_le _ _).trans ((add_le_add (hp.2.2 k j) (h2 k j)).trans_eq (by ring))⟩

#print axioms exists_family_nativeL2HalfAllScale_H2_bounds
end Yamabe3.Analysis.SpherePolar
