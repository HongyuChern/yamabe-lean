import Yamabe3.Analysis.NativeAngularThreeHalvesRecovery
import Yamabe3.Analysis.SpectralL2PotentialEntranceRegularity

/-! The actual native entrance of the same L2 potential inverse belongs
to the three-halves spectral scale and has a genuine H1 lift. Bounds are
uniform in the source and in the time of evaluation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem nativeAngular_synthesis_three_halves_bound (c : SpectralSpace AngularIndex)
    (hc : Summable (fun i => nativeAngularRate i^3*(c i)^2)) :
    NativeAngularSpectralRegular (3/2) (angularBasis.repr.symm c) ∧
      (∑' i,nativeAngularWeightedSquare (3/2) (angularBasis.repr.symm c) i) ≤
        8*(∑' i,nativeAngularRate i^3*(c i)^2) := by
  have hb (i : AngularIndex) :
      nativeAngularWeightedSquare (3/2) (angularBasis.repr.symm c) i ≤
        8*(nativeAngularRate i^3*(c i)^2) := by
    rw [nativeAngularWeightedSquare_three_halves,←HilbertBasis.repr_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    have hp := pow_le_pow_left₀ (angularEnergyWeight_pos i).le (angularEnergyWeight_le_two_rate i) 3
    have h := mul_le_mul_of_nonneg_right hp (sq_nonneg (c i))
    exact h.trans_eq (by ring)
  have hm := hc.mul_left 8
  have hs : NativeAngularSpectralRegular (3/2) (angularBasis.repr.symm c) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hm
  refine ⟨hs,?_⟩
  rw [←tsum_mul_left]
  exact Summable.tsum_le_tsum hb hs hm

theorem nativeL2PotentialEntrance_three_halves {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) :
    let u := angularBasis.repr.symm (spectralL2PotentialContinuousCLM nativeAngularRate
      (by norm_num) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) V F t)
    NativeAngularSpectralRegular (3/2) u ∧
      (∑' i,nativeAngularWeightedSquare (3/2) u i) ≤
        (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖F‖^2 := by
  obtain ⟨hc,hb⟩ := spectralL2PotentialContinuous_entrance_regular nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa only [neg_neg] using hplus) F t
  obtain ⟨hr,hbound⟩ := nativeAngular_synthesis_three_halves_bound _ hc
  refine ⟨hr,hbound.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤8)
  exact h.trans_eq (by norm_num; ring)

theorem nativeL2PotentialEntrance_exists_same_H1 {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) :
    let u := angularBasis.repr.symm (spectralL2PotentialContinuousCLM nativeAngularRate
      (by norm_num) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) V F t)
    ∃ b : AngularH1, angularEmbedding b=u ∧
      NativeAngularSpectralRegular (3/2) (angularEmbedding b) ∧
      (∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ≤
        (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖F‖^2 ∧
      ‖b‖^2 ≤ (50/9)*(1+‖V‖*((1-κ)⁻¹*(4/9)))^2*‖F‖^2 := by
  obtain ⟨hr,hbound⟩ := nativeL2PotentialEntrance_three_halves hκ0 hκ1 V hminus hplus F t
  obtain ⟨b,hb,hbn⟩ := nativeAngular_three_halves_exists_H1 _ hr
  exact ⟨b,hb,by simpa only [hb] using hr,by simpa only [hb] using hbound,hbn.trans hbound⟩

#print axioms nativeAngular_synthesis_three_halves_bound
#print axioms nativeL2PotentialEntrance_three_halves
#print axioms nativeL2PotentialEntrance_exists_same_H1
end Yamabe3.Analysis.Delaunay
