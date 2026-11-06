import Yamabe3.Analysis.NativeL2HalfCollar

/-! Uniform L2-source bounds for the actual zero-entrance H2 collar.
All constants precede the source. The value and the two weak jets are
exactly those of the same particular-minus-Poisson physical field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

private theorem bound_norm_from_square {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) {C : ℝ} (hC : 0≤C) (h : ‖y‖^2≤C*‖x‖^2) : ‖y‖≤Real.sqrt C*‖x‖ := by
  have hs : (Real.sqrt C*‖x‖)^2=C*‖x‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  have hn : 0≤Real.sqrt C*‖x‖ := by positivity
  nlinarith [norm_nonneg y]

theorem exists_nativeL2HalfCollar_uniform_bounds (P : NativeHighPotential)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ) :
    ∃ (C : ℝ) (G : Fin 3 → ℝ) (K : Fin 3 → Fin 3 → ℝ),0≤C ∧ (∀ j,0≤G j) ∧ (∀ k j,0≤K k j) ∧
      ∀ F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ),
      ‖nativeL2HalfCollarValue P hplus F‖≤C*‖F‖ ∧
      (∀ j,‖nativeL2HalfCollarFirst P hplus F j‖≤G j*‖F‖) ∧
      (∀ k j,‖nativeL2HalfCollarSecond P hplus F k j‖≤K k j*‖F‖) := by
  obtain ⟨G,K,hG,hK,hb⟩ := exists_nativePoissonCollar_H2_norm_bounds P
  let B := (50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2
  have hB : 0≤B := by dsimp [B];positivity
  let D := 12000*Real.exp 2*(4+P.derivativeBound)
  have hD : 0≤D := by have h := P.derivativeBound_nonneg;dsimp [D];positivity
  let T := nativeL2ParticularValueCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus
  let T1 := nativeL2ParticularFirstCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus
  let T2 := nativeL2ParticularSecondCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus
  refine ⟨‖T‖+Real.sqrt (D*B),fun j => ‖T1 j‖+Real.sqrt (G*B),
    fun k j => ‖T2 k j‖+Real.sqrt (K k*B),by positivity,fun j => by positivity,fun k j => by positivity,?_⟩
  intro F
  let b := nativeL2HalfEntrance P hplus F
  have he := nativeL2EntranceH1_spec P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus F
  have heB : (∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)≤B*‖F‖^2 := he.2.2.1
  have hp := hb b he.2.1
  have hp0 : ‖nativePoissonCollarValue P b‖≤Real.sqrt (D*B)*‖F‖ := by
    apply bound_norm_from_square F _ (mul_nonneg hD hB)
    exact hp.1.trans ((mul_le_mul_of_nonneg_left heB hD).trans_eq (by ring))
  have hp1 (j : Fin 3) : ‖nativePoissonCollarFirst P b j‖≤Real.sqrt (G*B)*‖F‖ := by
    apply bound_norm_from_square F _ (mul_nonneg hG hB)
    exact (hp.2.1 j).trans ((mul_le_mul_of_nonneg_left heB hG).trans_eq (by ring))
  have hp2 (k j : Fin 3) : ‖nativePoissonCollarSecond P b k j‖≤Real.sqrt (K k*B)*‖F‖ := by
    apply bound_norm_from_square F _ (mul_nonneg (hK k) hB)
    exact (hp.2.2 k j).trans ((mul_le_mul_of_nonneg_left heB (hK k)).trans_eq (by ring))
  constructor
  · exact (norm_sub_le (T F) (nativePoissonCollarValue P b)).trans
      ((add_le_add (T.le_opNorm F) hp0).trans_eq (by ring))
  constructor
  · intro j
    exact (norm_sub_le (T1 j F) (nativePoissonCollarFirst P b j)).trans
      ((add_le_add ((T1 j).le_opNorm F) (hp1 j)).trans_eq (by ring))
  · intro k j
    exact (norm_sub_le (T2 k j F) (nativePoissonCollarSecond P b k j)).trans
      ((add_le_add ((T2 k j).le_opNorm F) (hp2 k j)).trans_eq (by ring))

#print axioms exists_nativeL2HalfCollar_uniform_bounds
end Yamabe3.Analysis.SpherePolar
