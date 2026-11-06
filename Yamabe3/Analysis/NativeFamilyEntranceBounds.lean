import Yamabe3.Analysis.NativePoissonAllScaleH2
import Yamabe3.Analysis.NativeL2ShiftedCollar

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

theorem exists_family_nativeL2_shifted_collar_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀ k,0≤K k) ∧
      ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
        (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (s : ℝ),
      let Vs := boundedTimeTranslate ℝ s P.potential
      let Fs := l2TimeTranslateCLM (SpectralSpace AngularIndex) s F
      ‖nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one Vs
        (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hp s) Fs‖≤C*‖F‖ ∧
      (∀ j,‖nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one Vs
        (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hp s) j Fs‖≤G*‖F‖) ∧
      (∀ k j,‖nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one Vs
        (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hp s) k j Fs‖≤K k*‖F‖) := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_uniform_nativeL2Particular_collar_bounds hκ0 hκ1 hM
  refine ⟨C,G,K,hC,hG,hK,?_⟩
  intro P hP hPM hp F s
  subst κ
  have hs := h (boundedTimeTranslate ℝ s P.potential)
    ((le_of_eq (boundedTimeTranslate_norm ℝ s P.potential)).trans hPM)
    (translated_kernel_bound P.potential P.kernel_bound s) (translated_kernel_bound P.potential hp s)
    (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F)
  simpa only [l2TimeTranslate_norm] using hs

theorem exists_family_nativeShiftedEntrance_H2_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ (C G : ℝ) (K : Fin 3 → ℝ),0≤C ∧ 0≤G ∧ (∀ k,0≤K k) ∧
      ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (s : ℝ),s≤2 → ∀ (b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) →
        ‖nativeShiftedEntranceValue P s b‖^2≤C*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ∧
        (∀ j,‖nativeShiftedEntranceFirst P s b j‖^2≤G*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) ∧
        (∀ k j,‖nativeShiftedEntranceSecond P s b k j‖^2≤K k*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) := by
  obtain ⟨G,K,hG,hK,h⟩ := exists_nativeC2Collar_series_norm_bounds (ι := AngularIndex)
  let D := 12000*Real.exp 2*Real.exp 8*(4+(1+(10/9:ℝ)*M/(1-κ)))
  have hD : 0≤D := by dsimp only [D];positivity
  refine ⟨D,G*D,fun k => K k*D,hD,mul_nonneg hG hD,fun k => mul_nonneg (hK k) hD,?_⟩
  intro P hP hPM s hs b hb
  apply h _ (nativeShiftedEntranceMode_C2 P s b) _ hb (fun i => sq_nonneg _) D hD
  intro m
  have hd : P.derivativeBound≤1+(10/9:ℝ)*M/(1-κ) := by
    unfold NativeHighPotential.derivativeBound
    rw [hP]
    gcongr
  apply (nativeShiftedEntranceMode_budget P s hs b m).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  dsimp only [D]
  gcongr

theorem exists_family_nativePoissonL2CorrectionSource_bound {M : ℝ} (hM : 0≤M) :
    ∃ C : ℝ,0≤C ∧ ∀ (P : NativeHighPotential),‖P.potential‖≤M →
      ∀ b : AngularH1,‖nativePoissonL2CorrectionSource P b‖≤C*‖b‖ := by
  obtain ⟨C,hC,h⟩ := exists_spectralFullBoundaryPoisson_L2_bound nativeAngularRate
    (by norm_num) nativeAngularRate_lower
  refine ⟨M*C,mul_nonneg hM hC,?_⟩
  intro P hPM b
  unfold nativePoissonL2CorrectionSource
  rw [spectralBoundaryPotentialSource_eq_mul]
  apply (spectralL2PotentialMul_norm_le P.potential _).trans
  have hc := (h (nativePoissonAuxiliary P b)).trans
    (mul_le_mul_of_nonneg_left (nativePoissonAuxiliary_norm_le P b) hC)
  calc
    _ ≤ M*(C*‖b‖) := mul_le_mul hPM hc (norm_nonneg _) hM
    _ = (M*C)*‖b‖ := by ring

#print axioms exists_family_nativeL2_shifted_collar_bounds
#print axioms exists_family_nativeShiftedEntrance_H2_bounds
#print axioms exists_family_nativePoissonL2CorrectionSource_bound
end Yamabe3.Analysis.SpherePolar
