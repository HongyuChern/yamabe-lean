import Yamabe3.Analysis.NativeAngularThreeHalvesRecovery
import Yamabe3.Analysis.NativeHighDtNWeightedRegularity

/-! Explicit half-order spectral identities and bounded elementary
operations. These concern the original angular Hilbert basis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem nativeAngularWeightedSquare_one_half (f : AngularL2) (i : AngularIndex) :
    nativeAngularWeightedSquare (1/2) f i=angularEnergyWeight i*(inner ℝ (angularBasis i) f)^2 := by
  have he : (angularEnergyWeight i^(1/2:ℝ))^2=angularEnergyWeight i := by
    rw [←Real.rpow_two,←Real.rpow_mul (angularEnergyWeight_pos i).le]
    norm_num
  unfold nativeAngularWeightedSquare
  rw [mul_pow,he]

theorem nativeAngular_synthesis_one_half_bound (c : SpectralSpace AngularIndex)
    (hc : Summable (fun i => nativeAngularRate i*(c i)^2)) :
    NativeAngularSpectralRegular (1/2) (angularBasis.repr.symm c) ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (angularBasis.repr.symm c) i)≤
        2*(∑' i,nativeAngularRate i*(c i)^2) := by
  have hb (i : AngularIndex) : nativeAngularWeightedSquare (1/2) (angularBasis.repr.symm c) i≤
      2*(nativeAngularRate i*(c i)^2) := by
    rw [nativeAngularWeightedSquare_one_half,←HilbertBasis.repr_apply_apply,LinearIsometryEquiv.apply_symm_apply]
    exact (mul_le_mul_of_nonneg_right (angularEnergyWeight_le_two_rate i) (sq_nonneg _)).trans_eq (by ring)
  have hm := hc.mul_left 2
  have hs : NativeAngularSpectralRegular (1/2) (angularBasis.repr.symm c) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hm
  refine ⟨hs,?_⟩
  rw [←tsum_mul_left]
  exact Summable.tsum_le_tsum hb hs hm

theorem nativeAngular_three_halves_to_half (f : AngularL2)
    (hf : NativeAngularSpectralRegular (3/2) f) :
    NativeAngularSpectralRegular (1/2) f ∧
      (∑' i,nativeAngularWeightedSquare (1/2) f i)≤∑' i,nativeAngularWeightedSquare (3/2) f i := by
  have hb (i : AngularIndex) : nativeAngularWeightedSquare (1/2) f i≤nativeAngularWeightedSquare (3/2) f i := by
    rw [nativeAngularWeightedSquare_one_half,nativeAngularWeightedSquare_three_halves]
    have hw := angularEnergyWeight_one_le i
    have hpow : angularEnergyWeight i≤angularEnergyWeight i^3 := by nlinarith [sq_nonneg (angularEnergyWeight i-1)]
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  have hs : NativeAngularSpectralRegular (1/2) f :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hf
  exact ⟨hs,Summable.tsum_le_tsum hb hs hf⟩

theorem nativeAngularSpectralRegular_smul {s : ℝ} {f : AngularL2}
    (hf : NativeAngularSpectralRegular s f) (c : ℝ) :
    NativeAngularSpectralRegular s (c • f) ∧
      (∑' i,nativeAngularWeightedSquare s (c • f) i)=c^2*(∑' i,nativeAngularWeightedSquare s f i) := by
  have he (i : AngularIndex) : nativeAngularWeightedSquare s (c • f) i=c^2*nativeAngularWeightedSquare s f i := by
    unfold nativeAngularWeightedSquare
    rw [real_inner_smul_right]
    ring
  change Summable (fun i => nativeAngularWeightedSquare s (c • f) i) ∧ _
  simp_rw [he]
  exact ⟨hf.mul_left _,tsum_mul_left⟩

theorem nativeAngularSpectralRegular_high {s : ℝ} {f : AngularL2}
    (hf : NativeAngularSpectralRegular s f) :
    NativeAngularSpectralRegular s (nativeHighProjection f) ∧
      (∑' i,nativeAngularWeightedSquare s (nativeHighProjection f) i)≤∑' i,nativeAngularWeightedSquare s f i := by
  have hb (i : AngularIndex) : nativeAngularWeightedSquare s (nativeHighProjection f) i≤nativeAngularWeightedSquare s f i := by
    unfold nativeAngularWeightedSquare nativeHighProjection
    rw [nativeAngularProjection_coefficient]
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,zero_pow (by norm_num : 2≠0)]
      positivity
  have hs : NativeAngularSpectralRegular s (nativeHighProjection f) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hf
  exact ⟨hs,Summable.tsum_le_tsum hb hs hf⟩

#print axioms nativeAngularWeightedSquare_one_half
#print axioms nativeAngular_synthesis_one_half_bound
#print axioms nativeAngular_three_halves_to_half
#print axioms nativeAngularSpectralRegular_smul
#print axioms nativeAngularSpectralRegular_high
end Yamabe3.Analysis.Delaunay
