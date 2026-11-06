import Yamabe3.Analysis.NativeHighCoupledWeightedRegularity

/-! Reconstruct the actual native H1 element from a proved three-halves
angular spectral budget. The energy-space witness is produced by its
existing Hilbert basis, not supplied as an extra boundary input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem angularEnergyWeight_one_le (i : AngularIndex) : 1 ≤ angularEnergyWeight i := by
  have hn : 0 ≤ angularEigenvalue i := by
    rcases angularEigenvalue_zero_two_or_ge_six i with h|h|h <;> linarith
  have hs := angularEnergyWeight_sq i
  have hp := angularEnergyWeight_pos i
  nlinarith

theorem angularEnergyWeight_le_two_rate (i : AngularIndex) :
    angularEnergyWeight i ≤ 2*nativeAngularRate i := by
  have hs := angularEnergyWeight_sq i
  have hr := nativeAngularRate_sq i
  have hp := angularEnergyWeight_pos i
  have hq := nativeAngularRate_lower i
  have hm := le_max_right (6:ℝ) (angularEigenvalue i)
  have hm0 := le_max_left (6:ℝ) (angularEigenvalue i)
  nlinarith

theorem nativeAngularWeightedSquare_three_halves (f : AngularL2) (i : AngularIndex) :
    nativeAngularWeightedSquare (3/2) f i =
      angularEnergyWeight i^3*(inner ℝ (angularBasis i) f)^2 := by
  have he : (angularEnergyWeight i^(3/2:ℝ))^2=angularEnergyWeight i^3 := by
    rw [←Real.rpow_two,←Real.rpow_mul (angularEnergyWeight_pos i).le]
    norm_num
  unfold nativeAngularWeightedSquare
  rw [mul_pow,he]

theorem nativeAngular_three_halves_exists_H1 (f : AngularL2)
    (hf : NativeAngularSpectralRegular (3/2) f) :
    ∃ b : AngularH1, angularEmbedding b=f ∧
      ‖b‖^2 ≤ ∑' i,nativeAngularWeightedSquare (3/2) f i := by
  let c := fun i => angularEnergyWeight i*inner ℝ (angularBasis i) f
  have hbound (i : AngularIndex) : (c i)^2 ≤ nativeAngularWeightedSquare (3/2) f i := by
    rw [nativeAngularWeightedSquare_three_halves]
    dsimp [c]
    rw [mul_pow]
    have hw := angularEnergyWeight_one_le i
    nlinarith [mul_nonneg (sq_nonneg (angularEnergyWeight i)) (sub_nonneg.mpr hw),
      mul_nonneg (sq_nonneg (inner ℝ (angularBasis i) f))
        (mul_nonneg (sq_nonneg (angularEnergyWeight i)) (sub_nonneg.mpr hw))]
  have hs : Summable (fun i => (c i)^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hbound hf
  have hc : Memℓp c 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hs
  let b := angularEnergyBasis.repr.symm (⟨c,hc⟩ : SpectralSpace AngularIndex)
  have hb : angularEmbedding b=f := by
    apply angularBasis.repr.injective
    ext i
    rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply]
    have h := (angularEnergyBasis_synthesis_spec (⟨c,hc⟩ : SpectralSpace AngularIndex)).1 i
    change inner ℝ (angularBasis i) (angularEmbedding b)=c i/angularEnergyWeight i at h
    rw [h]
    dsimp [c]
    field_simp [(angularEnergyWeight_pos i).ne']
  refine ⟨b,hb,?_⟩
  have he := angularEnergyBasis_hasSum_energy b
  have hcoeff (i : AngularIndex) :
      (1+angularEigenvalue i)*(inner ℝ (angularBasis i) (angularEmbedding b))^2=(c i)^2 := by
    rw [hb,←angularEnergyWeight_sq]
    simp only [c,mul_pow]
  simp only [hcoeff] at he
  rw [←he.tsum_eq]
  exact Summable.tsum_le_tsum hbound hs hf

#print axioms angularEnergyWeight_one_le
#print axioms angularEnergyWeight_le_two_rate
#print axioms nativeAngularWeightedSquare_three_halves
#print axioms nativeAngular_three_halves_exists_H1
end Yamabe3.Analysis.Delaunay
