import Yamabe3.Analysis.NativeHighPoissonEntranceExtension
import Yamabe3.Analysis.NativeHighPoissonSecondSpectral
import Yamabe3.Analysis.HalfLineC2ReflectionEnergy

/-! Whole-line mixed second energy of the same actual entrance
extension, with a numerical constant uniform in all frequencies. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def nativePoissonReflectedSecondEnergy (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) : ℝ :=
  let z := nativePoissonEntranceExtension P b i
  let w := angularEnergyWeight i
  w^4*(∫ t : ℝ,z t^2)+w^2*(∫ t : ℝ,deriv z t^2)+(∫ t : ℝ,deriv (deriv z) t^2)

theorem NativeHighPotential.reflected_energy_high (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) (hi : 6 ≤ angularEigenvalue i) :
    let z := nativePoissonEntranceExtension P b i
    Integrable (fun t => z t^2) ∧ Integrable (fun t => deriv z t^2) ∧
      Integrable (fun t => deriv (deriv z) t^2) ∧
      nativePoissonReflectedSecondEnergy P b i ≤ 4000*nativePoissonSecondTimeEnergy P b i := by
  let f := nativePoissonCoordinate P b i
  let df := fun t => inner ℝ (angularBasis i) (P.curveDerivative b t)
  let ddf := fun t => (nativeAngularRate i^2-P.potential t)*f t
  have h1 : (fun t => deriv f t^2) =ᵐ[volume.restrict (Ioi 0)] (fun t => df t^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [P.coordinate_deriv b i t ht]
  have h2 : (fun t => deriv (deriv f) t^2) =ᵐ[volume.restrict (Ioi 0)] (fun t => ddf t^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : deriv (deriv f) t = (angularEigenvalue i+1/4-P.potential t)*f t :=
      P.curve_coefficient_equation b i t ht
    dsimp only [ddf]
    rw [he,nativeAngularRate_sq,max_eq_right hi]
  have hE := halfLineC2Extension_energy (f := f) (df := df) (ddf := ddf)
    (fun t ht => (innerSL ℝ (angularBasis i)).hasFDerivAt.comp_hasDerivWithinAt t
      (nativeHalfHighPotentialPhysical_hasDerivWithinAt P.κ_nonneg P.κ_lt_one
        P.potential P.kernel_bound P.nonneg b t ht))
    (P.coordinate_second_right_jet b i)
    (((continuous_const.sub P.potential.continuous).mul (P.coordinate_continuous b i)).continuousOn)
    (P.curve_coefficient_square_integral b i).1
    ((P.coordinate_first_energy b i hi).1.congr h1)
    ((P.coordinate_second_energy b i hi).1.congr h2)
  dsimp only at hE
  rw [← integral_congr_ae h1,← integral_congr_ae h2] at hE
  refine ⟨hE.1.1,hE.2.1.1,hE.2.2.1,?_⟩
  have h0 := mul_le_mul_of_nonneg_left hE.1.2 (pow_nonneg (angularEnergyWeight_pos i).le 4)
  have h1b := mul_le_mul_of_nonneg_left hE.2.1.2 (sq_nonneg (angularEnergyWeight i))
  have h2b := hE.2.2.2
  unfold nativePoissonReflectedSecondEnergy nativePoissonSecondTimeEnergy
  dsimp only [nativePoissonEntranceExtension]
  nlinarith only [h0,h1b,h2b]

theorem NativeHighPotential.entranceExtension_low_zero (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) (hi : angularEigenvalue i < 6) :
    nativePoissonEntranceExtension P b i = fun _ => 0 := by
  unfold nativePoissonEntranceExtension
  rw [P.coordinate_low_zero b i hi]
  funext t
  simp only [halfLineC2Extension,halfLineReflection,mul_zero,Finset.sum_const_zero,ite_self]

theorem NativeHighPotential.reflected_energy_spectral_bound (P : NativeHighPotential)
    (b : AngularH1) (i : AngularIndex) :
    let z := nativePoissonEntranceExtension P b i
    Integrable (fun t => z t^2) ∧ Integrable (fun t => deriv z t^2) ∧
      Integrable (fun t => deriv (deriv z) t^2) ∧
      nativePoissonReflectedSecondEnergy P b i ≤
        (4000*(4+P.derivativeBound))*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  by_cases hi : 6 ≤ angularEigenvalue i
  · have h := P.reflected_energy_high b i hi
    refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (P.second_energy_spectral_bound b i) (by norm_num)).trans_eq (by ring)
  · have he := P.entranceExtension_low_zero b i (lt_of_not_ge hi)
    dsimp only
    refine ⟨?_,?_,?_,?_⟩
    · rw [he]; simp only [zero_pow (by decide : 2 ≠ 0)]; exact integrable_zero _ _ _
    · rw [he]; simp only [deriv_const',Pi.zero_apply,zero_pow (by decide : 2 ≠ 0)]; exact integrable_zero _ _ _
    · rw [he]; simp only [deriv_const',Pi.zero_apply,zero_pow (by decide : 2 ≠ 0)]; exact integrable_zero _ _ _
    · unfold nativePoissonReflectedSecondEnergy
      rw [he]
      simp only [deriv_const',Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),integral_zero,mul_zero,add_zero]
      have hC := P.derivativeBound_nonneg
      have hw : 0 ≤ nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := sq_nonneg _
      positivity

theorem NativeHighPotential.reflected_energy_summable (P : NativeHighPotential)
    (b : AngularH1) (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    Summable (nativePoissonReflectedSecondEnergy P b) ∧
      (∑' i,nativePoissonReflectedSecondEnergy P b i) ≤
        (4000*(4+P.derivativeBound))*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have hn (i : AngularIndex) : 0 ≤ nativePoissonReflectedSecondEnergy P b i := by
    unfold nativePoissonReflectedSecondEnergy
    dsimp only
    positivity
  have hm := hb.mul_left (4000*(4+P.derivativeBound))
  have hs := Summable.of_nonneg_of_le hn (fun i => (P.reflected_energy_spectral_bound b i).2.2.2) hm
  refine ⟨hs,?_⟩
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => (P.reflected_energy_spectral_bound b i).2.2.2) hs hm

#print axioms NativeHighPotential.reflected_energy_high
#print axioms NativeHighPotential.entranceExtension_low_zero
#print axioms NativeHighPotential.reflected_energy_spectral_bound
#print axioms NativeHighPotential.reflected_energy_summable
end Yamabe3.Analysis.Delaunay
