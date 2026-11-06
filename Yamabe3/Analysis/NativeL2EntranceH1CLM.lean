import Yamabe3.Analysis.NativeL2PotentialEntrance

/-! Bounded linear lifting of the actual same-potential L2 entrance to
the pre-existing native H1 completion. Uniqueness of the true inclusion
proves linearity of the constructed lift. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

def nativeL2EntranceH1 (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) : AngularH1 :=
  (nativeL2PotentialEntrance_exists_same_H1 hκ0 hκ1 V hminus hplus F 0).choose

theorem nativeL2EntranceH1_spec (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    angularEmbedding (nativeL2EntranceH1 hκ0 hκ1 V hminus hplus F)=
      angularBasis.repr.symm (spectralL2PotentialEntranceCLM nativeAngularRate
        (by norm_num) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) V F) ∧
    NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeL2EntranceH1 hκ0 hκ1 V hminus hplus F)) ∧
    (∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeL2EntranceH1 hκ0 hκ1 V hminus hplus F)) i)≤
      (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖F‖^2 ∧
    ‖nativeL2EntranceH1 hκ0 hκ1 V hminus hplus F‖^2≤
      (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖F‖^2 :=
  (nativeL2PotentialEntrance_exists_same_H1 hκ0 hκ1 V hminus hplus F 0).choose_spec

theorem nativeL2EntranceH1_norm_le (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    ‖nativeL2EntranceH1 hκ0 hκ1 V hminus hplus F‖ ≤
      Real.sqrt (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))*‖F‖ := by
  have h := (nativeL2EntranceH1_spec hκ0 hκ1 V hminus hplus F).2.2.2
  have hp : 0≤1+‖V‖*((1-κ)⁻¹*(4/9)) := by positivity
  have hsq : (Real.sqrt (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))*‖F‖)^2=
      (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖F‖^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤50/9)]
  have hn : 0≤Real.sqrt (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))*‖F‖ := by positivity
  nlinarith [norm_nonneg (nativeL2EntranceH1 hκ0 hκ1 V hminus hplus F)]

def nativeL2EntranceH1CLM : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ] AngularH1 :=
  ({ toFun := nativeL2EntranceH1 hκ0 hκ1 V hminus hplus
     map_add' := by
       intro F G
       apply angularEmbedding_injective
       rw [map_add,(nativeL2EntranceH1_spec hκ0 hκ1 V hminus hplus (F+G)).1,
         (nativeL2EntranceH1_spec hκ0 hκ1 V hminus hplus F).1,
         (nativeL2EntranceH1_spec hκ0 hκ1 V hminus hplus G).1,map_add,map_add]
     map_smul' := by
       intro c F
       apply angularEmbedding_injective
       rw [map_smul,(nativeL2EntranceH1_spec hκ0 hκ1 V hminus hplus (c • F)).1,
         (nativeL2EntranceH1_spec hκ0 hκ1 V hminus hplus F).1,map_smul,map_smul]
       rfl
  } : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →ₗ[ℝ] AngularH1).mkContinuous
    (Real.sqrt (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9))))
    (by intro F;exact nativeL2EntranceH1_norm_le hκ0 hκ1 V hminus hplus F)

#print axioms nativeL2EntranceH1_spec
#print axioms nativeL2EntranceH1_norm_le
#print axioms nativeL2EntranceH1CLM
end Yamabe3.Analysis.Delaunay
