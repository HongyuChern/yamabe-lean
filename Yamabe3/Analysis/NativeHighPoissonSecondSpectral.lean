import Yamabe3.Analysis.NativeHighPoissonSecondEnergy
import Yamabe3.Analysis.NativeHighDtNWeightedRegularity

/-! Actual second-order mixed cylinder energy on the 3/2 value trace
scale. This is still a spectral/time result, not an asserted geometric
trace theorem. Low modes vanish in the actual curve, including derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem NativeHighPotential.coordinate_low_zero (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (hi : angularEigenvalue i < 6) :
    nativePoissonCoordinate P b i = fun _ => 0 :=
  funext (fun t => P.curve_low_zero b i hi t)

theorem NativeHighPotential.second_energy_spectral_bound
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    nativePoissonSecondTimeEnergy P b i ≤
      (4+P.derivativeBound)*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  have hw := angularEnergyWeight_pos i
  have hpow : ((angularEnergyWeight i)^(3/2:ℝ))^2 = angularEnergyWeight i^3 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hw.le]
    norm_num
  have he : nativeAngularWeightedSquare (3/2) (angularEmbedding b) i =
      angularEnergyWeight i^3*(inner ℝ (angularBasis i) (angularEmbedding b))^2 := by
    unfold nativeAngularWeightedSquare
    rw [mul_pow,hpow]
  rw [he]
  by_cases hi : 6 ≤ angularEigenvalue i
  · simpa only [mul_assoc] using P.coordinate_second_mixed_energy b i hi
  · unfold nativePoissonSecondTimeEnergy
    rw [P.coordinate_low_zero b i (lt_of_not_ge hi)]
    simp only [deriv_const', Pi.zero_apply, zero_pow (by decide : 2≠0), integral_zero,
      mul_zero, add_zero]
    have hC := P.derivativeBound_nonneg
    positivity

theorem NativeHighPotential.second_energy_summable
    (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    Summable (nativePoissonSecondTimeEnergy P b) ∧
      (∑' i, nativePoissonSecondTimeEnergy P b i) ≤
        (4+P.derivativeBound)*(∑' i, nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have hnon (i : AngularIndex) : 0 ≤ nativePoissonSecondTimeEnergy P b i := by
    unfold nativePoissonSecondTimeEnergy
    dsimp only
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (pow_nonneg (angularEnergyWeight_pos i).le 4) (integral_nonneg (fun _ => sq_nonneg _))
      · exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _))
    · exact integral_nonneg (fun _ => sq_nonneg _)
  have hm := hb.mul_left (4+P.derivativeBound)
  have hs := Summable.of_nonneg_of_le hnon (P.second_energy_spectral_bound b) hm
  refine ⟨hs, ?_⟩
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (P.second_energy_spectral_bound b) hs hm

/-- The precise same inverse witness works at the lower trace scale. -/
theorem nativeHighCoupled_poisson_second_mixed_bound
    (B W P : NativeHighPotential) (f : AngularL2)
    (hf : NativeAngularSpectralRegular (1/2) f) :
    let b := nativeHighCoupledDtNInverse B W f
    Summable (nativePoissonSecondTimeEnergy P b) ∧
      (∑' i, nativePoissonSecondTimeEnergy P b i) ≤
        4*(4+P.derivativeBound)*(∑' i, nativeAngularWeightedSquare (1/2) f i) := by
  obtain ⟨hb,hbb⟩ := nativeHighCoupled_inverse_spectral_regular B W (1/2) f hf
  have hb' : NativeAngularSpectralRegular (3/2)
      (angularEmbedding (nativeHighCoupledDtNInverse B W f)) := by
    convert hb using 1 <;> norm_num
  obtain ⟨hs,he⟩ := P.second_energy_summable (nativeHighCoupledDtNInverse B W f) hb'
  have hbb' : (∑' i, nativeAngularWeightedSquare (3/2)
      (angularEmbedding (nativeHighCoupledDtNInverse B W f)) i) ≤
      4*(∑' i,nativeAngularWeightedSquare (1/2) f i) := by
    convert hbb using 1 <;> norm_num
  refine ⟨hs,he.trans ?_⟩
  have hC := P.derivativeBound_nonneg
  have h := mul_le_mul_of_nonneg_left hbb' (by linarith : 0 ≤ 4+P.derivativeBound)
  convert h using 1 <;> ring

#print axioms NativeHighPotential.coordinate_low_zero
#print axioms NativeHighPotential.second_energy_spectral_bound
#print axioms NativeHighPotential.second_energy_summable
#print axioms nativeHighCoupled_poisson_second_mixed_bound
end Yamabe3.Analysis.Delaunay
