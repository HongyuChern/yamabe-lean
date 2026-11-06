import Yamabe3.Analysis.NativeSupportedOuterAllScale
import Yamabe3.Analysis.NativeLowCauchyUniformHalfEnd
import Yamabe3.Analysis.NativeSupportedLowAllScaleEquation
import Yamabe3.Analysis.NativeExteriorHalfEndJetBound

/-! Uniform actual jet bounds for the source and compensated low Cauchy
parts of the same supported exterior field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem exists_nativeBubbleParticular_all_scale_bound (τ : ℝ) :
    ∃L : ℝ,0≤L ∧ ∀(F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (s : ℝ),
      ‖nativeBubbleParticularAllScaleJetCLM τ s F‖≤L*‖F‖ := by
  let P := fullBubbleHighPotential τ
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_nativeL2_all_shifted_collar_uniform_bounds P.κ_nonneg P.κ_lt_one
    P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ)
  let L := 1+C+G+∑k : Fin 3,K k
  have hsum : 0≤∑k : Fin 3,K k := Finset.sum_nonneg (fun k _ => hK k)
  have hL : 0≤L := by dsimp [L];linarith
  have hCL : C≤L := by dsimp [L];linarith
  have hGL : G≤L := by dsimp [L];linarith
  have hKL (k : Fin 3) : K k≤L := by
    have hk := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ k)
    dsimp [L];linarith
  refine ⟨L,hL,fun F s => ?_⟩
  have hh := h F s
  have hh' : ‖(nativeBubbleParticularAllScaleJetCLM τ s F).val.1‖≤C*‖F‖ ∧
      (∀j,‖(nativeBubbleParticularAllScaleJetCLM τ s F).val.2.1 j‖≤G*‖F‖) ∧
      (∀k j,‖(nativeBubbleParticularAllScaleJetCLM τ s F).val.2.2 k j‖≤K k*‖F‖) := by
    let Q := fullBubbleHighPotential (τ+s)
    let hp := fullBubblePhasePotential_plus_kernel (τ+s)
    let Fs := l2TimeTranslateCLM AngularSpectralSpace s F
    change ‖nativeL2ParticularValueCLM Q.κ_nonneg Q.κ_lt_one Q.potential Q.kernel_bound hp Fs‖≤C*‖F‖ ∧
      (∀j,‖nativeL2ParticularFirstCLM Q.κ_nonneg Q.κ_lt_one Q.potential Q.kernel_bound hp j Fs‖≤G*‖F‖) ∧
      (∀k j,‖nativeL2ParticularSecondCLM Q.κ_nonneg Q.κ_lt_one Q.potential Q.kernel_bound hp k j Fs‖≤K k*‖F‖)
    simpa only [P,Q,Fs,fullBubbleHighPotential,←fullBubblePhasePotential_translate] using hh
  exact nativeCollarJet_norm_le_of_components _ (mul_nonneg hL (norm_nonneg _))
    (hh'.1.trans (mul_le_mul_of_nonneg_right hCL (norm_nonneg _)))
    (fun j => (hh'.2.1 j).trans (mul_le_mul_of_nonneg_right hGL (norm_nonneg _)))
    (fun k j => (hh'.2.2 k j).trans (mul_le_mul_of_nonneg_right (hKL k) (norm_nonneg _)))

theorem exists_nativeSupportedParticular_halfEnd_bound (τ b : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀(F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (s : ℝ),s≤0 →
      ‖nativeSupportedParticularJet τ b s F‖≤C*‖F‖ := by
  obtain ⟨C,hC,hc⟩ := exists_nativeBubbleParticular_all_scale_bound τ
  obtain ⟨D,hD,hd⟩ := exists_uniform_nativeSupportedLowAllScale_bound
  refine ⟨C+D*Real.exp (-4*b),by positivity,fun F s hs => ?_⟩
  have hl := (nativeSupportedLowAllScaleRawJetCLM (nativeBubbleReverseProfile τ)
    (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) b s).le_of_opNorm_le
    (hd _ _ _ b s) F
  have hex : Real.exp (4*(s-b))≤Real.exp (-4*b) := Real.exp_le_exp.mpr (by linarith)
  have hl' : ‖nativeLowReverseAllScaleJetCLM (nativeBubbleReverseProfile τ)
      (nativeBubbleReverseProfile_continuous τ) (nativeBubbleReverseProfile_bounds τ) s
        (nativeSupportedReverseSourcePrepareCLM b F)‖≤(D*Real.exp (-4*b))*‖F‖ :=
    hl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex hD.le) (norm_nonneg _))
  exact (norm_add_le _ _).trans ((add_le_add (hc F s) hl').trans_eq (by ring))

theorem exists_nativeSupportedLowCauchy_halfEnd_bound (b : ℝ) {τ : ℝ} (ht : 0<τ) :
    ∃C : ℝ,0≤C ∧ ∀(F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (d n : AngularL2)
      (s : ℝ),s≤0 → ‖nativeSupportedLowCauchyAllScaleJet b ht F d n s‖≤C*‖(F,(d,n))‖ := by
  obtain ⟨C,hC,h⟩ := exists_nativeLowCauchy_uniform_halfEnd_bound ht
  let T := nativeLowCauchyCoordinateCLM.comp ((nativeBubbleLowCorrectionDataCLM τ).comp
    (nativeSupportedLowPhysicalDataCLM b))
  refine ⟨C*‖T‖,mul_nonneg hC (norm_nonneg _),fun F d n s hs => ?_⟩
  have hh := h (T (F,(d,n))) s hs
  change ‖nativeSupportedLowCauchyAllScaleJet b ht F d n s‖≤C*‖T (F,(d,n))‖ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (T.le_opNorm _) hC).trans_eq (by ring))

#print axioms exists_nativeBubbleParticular_all_scale_bound
#print axioms exists_nativeSupportedParticular_halfEnd_bound
#print axioms exists_nativeSupportedLowCauchy_halfEnd_bound
end Yamabe3.Analysis.SpherePolar
