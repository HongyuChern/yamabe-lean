import Yamabe3.Analysis.NativeHighPoissonJetEnergy
import Yamabe3.Analysis.NativeHighCoupledWeightedRegularity

/-! The lower trace-scale estimate uses only the actual continuous
potential. It is independent of the stronger fourth-order coefficient
regularity hypotheses. The time derivatives are genuine derivatives of
the same curve and the displayed energies are actual integrals. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem NativeHighPotential.coordinate_second_energy
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) :
    IntegrableOn (fun t => deriv (deriv (nativePoissonCoordinate P b i)) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv (nativePoissonCoordinate P b i)) t^2) ≤
        2 * angularEnergyWeight i^3 *
          (inner ℝ (angularBasis i) (angularEmbedding b))^2 := by
  let z := nativePoissonCoordinate P b i
  let w := angularEnergyWeight i
  have hw : 0 < w := angularEnergyWeight_pos i
  have hzc : ContDiffOn ℝ 2 z (Ioi 0) := P.curve_coefficient_C2 b i
  have hdc : ContDiffOn ℝ 1 (deriv z) (Ioi 0) := hzc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hddc : ContDiffOn ℝ 0 (deriv (deriv z)) (Ioi 0) := hdc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hb (t : ℝ) (ht : t ∈ Ioi 0) : deriv (deriv z) t^2 ≤ w^4*z t^2 := by
    have heq : deriv (deriv z) t = (angularEigenvalue i+1/4-P.potential t)*z t :=
      P.curve_coefficient_equation b i t ht
    rw [heq]
    have hq0 : 0 ≤ angularEigenvalue i+1/4-P.potential t := by
      linarith only [hi, P.upper t ht.le]
    have hqw : angularEigenvalue i+1/4-P.potential t ≤ w^2 := by
      dsimp only [w]
      rw [angularEnergyWeight_sq]
      linarith only [P.nonneg t]
    have hq2 : (angularEigenvalue i+1/4-P.potential t)^2 ≤ w^4 := by
      have h := mul_self_le_mul_self hq0 hqw
      nlinarith only [h]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
  have hzI := (P.curve_coefficient_square_integral b i).1
  have hm := hzI.const_mul (w^4)
  have hiI : IntegrableOn (fun t => deriv (deriv z) t^2) (Ioi 0) := by
    apply hm.mono' ((hddc.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb t ht
  refine ⟨hiI, ?_⟩
  have he := integral_mono_ae hiI hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hb t ht)
  rw [integral_const_mul] at he
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (P.curve_coefficient_square_integral b i).2
    (pow_nonneg hw.le 4)).trans_eq
  change w^4*((2/w)*(inner ℝ (angularBasis i) (angularEmbedding b))^2)=_
  field_simp [hw.ne']
  <;> ring

def nativePoissonSecondTimeEnergy (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) : ℝ :=
  let z := nativePoissonCoordinate P b i
  let w := angularEnergyWeight i
  w^4*(∫ t : ℝ in Ioi 0, z t^2)+w^2*(∫ t : ℝ in Ioi 0, deriv z t^2)+
    (∫ t : ℝ in Ioi 0, deriv (deriv z) t^2)

theorem NativeHighPotential.coordinate_second_mixed_energy
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i) :
    nativePoissonSecondTimeEnergy P b i ≤
      (4+P.derivativeBound)*angularEnergyWeight i^3*
        (inner ℝ (angularBasis i) (angularEmbedding b))^2 := by
  let w := angularEnergyWeight i
  let a := inner ℝ (angularBasis i) (angularEmbedding b)
  have hw : 0 < w := angularEnergyWeight_pos i
  have h0 := mul_le_mul_of_nonneg_left (P.curve_coefficient_square_integral b i).2
    (pow_nonneg hw.le 4)
  have h1 := mul_le_mul_of_nonneg_left (P.coordinate_first_energy b i hi).2 (sq_nonneg w)
  have h2 := (P.coordinate_second_energy b i hi).2
  have he : w^4*((2/w)*a^2)=2*w^3*a^2 := by
    field_simp [hw.ne']
    <;> ring
  change w^4*(∫ t : ℝ in Ioi 0, (nativePoissonCoordinate P b i t)^2) ≤ w^4*((2/w)*a^2) at h0
  rw [he] at h0
  unfold nativePoissonSecondTimeEnergy
  dsimp only
  change w^2*(∫ t : ℝ in Ioi 0, deriv (nativePoissonCoordinate P b i) t^2) ≤
    w^2*(P.derivativeBound*w*a^2) at h1
  change (∫ t : ℝ in Ioi 0, deriv (deriv (nativePoissonCoordinate P b i)) t^2) ≤2*w^3*a^2 at h2
  dsimp only [w,a] at h0 h1 h2
  nlinarith only [h0,h1,h2]

#print axioms NativeHighPotential.coordinate_second_energy
#print axioms NativeHighPotential.coordinate_second_mixed_energy
end Yamabe3.Analysis.Delaunay
