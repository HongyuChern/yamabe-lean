import Yamabe3.Analysis.NativeHighPoissonEnergy
import Yamabe3.Analysis.HalfEndScalarJetEnergy

/-! Higher time energies of the identical native Poisson coefficient.
Coefficient jet assumptions are exposed here and are discharged for the
actual Delaunay/bubble instances separately. No solution jet is input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def nativePoissonCoordinate (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) : ℝ → ℝ :=
  fun t => inner ℝ (angularBasis i) (P.curve b t)

theorem NativeHighPotential.coordinate_deriv (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (t : ℝ) (ht : 0 < t) :
    deriv (nativePoissonCoordinate P b i) t = inner ℝ (angularBasis i) (P.curveDerivative b t) := by
  exact ((innerSL ℝ (angularBasis i)).hasFDerivAt.comp_hasDerivAt t
    (nativeHalfHighPotentialPhysical_hasDerivAt P.κ_nonneg P.κ_lt_one P.potential
      P.kernel_bound P.nonneg b t ht)).deriv

theorem NativeHighPotential.coordinate_first_energy (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (hi : 6 ≤ angularEigenvalue i) :
    IntegrableOn (fun t => deriv (nativePoissonCoordinate P b i) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (nativePoissonCoordinate P b i) t^2) ≤
        P.derivativeBound * angularEnergyWeight i *
          (inner ℝ (angularBasis i) (angularEmbedding b))^2 := by
  have h := P.curve_derivative_square_integral b i hi
  have he : (fun t => (inner ℝ (angularBasis i) (P.curveDerivative b t))^2)
      =ᵐ[volume.restrict (Ioi 0)] (fun t => deriv (nativePoissonCoordinate P b i) t^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [P.coordinate_deriv b i t ht]
  exact ⟨h.1.congr he, (integral_congr_ae he).symm.trans_le h.2⟩

theorem NativeHighPotential.coordinate_higher_jet_energy
    (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex)
    (hi : 6 ≤ angularEigenvalue i)
    (hVs : ContDiff ℝ 2 (fun t : ℝ => P.potential t)) (K : ℝ)
    (hV1 : ∀ t : ℝ, 0 < t → (deriv (fun s => P.potential s) t)^2 ≤ K^2)
    (hV2 : ∀ t : ℝ, 0 < t → (deriv (deriv (fun s => P.potential s)) t)^2 ≤ K^2) :
    let z := nativePoissonCoordinate P b i
    let W := angularEnergyWeight i
    ContDiffOn ℝ 4 z (Ioi 0) ∧
    (IntegrableOn (fun t => deriv (deriv z) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv z) t^2) ≤ W^4*(∫ t : ℝ in Ioi 0, z t^2)) ∧
    (IntegrableOn (fun t => deriv (deriv (deriv z)) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv (deriv z)) t^2) ≤
        2*K^2*(∫ t : ℝ in Ioi 0, z t^2)+2*W^4*(∫ t : ℝ in Ioi 0, deriv z t^2)) ∧
    (IntegrableOn (fun t => deriv (deriv (deriv (deriv z))) t^2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, deriv (deriv (deriv (deriv z))) t^2) ≤
        3*(K^2+W^8)*(∫ t : ℝ in Ioi 0, z t^2)+12*K^2*(∫ t : ℝ in Ioi 0, deriv z t^2)) := by
  let q : ℝ → ℝ := fun t => angularEigenvalue i+1/4-P.potential t
  have hq : ContDiff ℝ 2 q := contDiff_const.sub hVs
  have hqD : deriv q = fun t => -deriv (fun s => P.potential s) t := by
    funext t
    exact ((hasDerivAt_const t (angularEigenvalue i+1/4)).sub
      ((hVs.differentiable (by norm_num) t).hasDerivAt)).deriv.trans (by ring)
  have hqDD : deriv (deriv q) = fun t => -deriv (deriv (fun s => P.potential s)) t := by
    rw [hqD]
    funext t
    exact deriv.neg
  apply scalar_ode_higher_jet_energy (P.curve_coefficient_C2 b i) hq.contDiffOn
    (P.curve_coefficient_equation b i)
    (P.curve_coefficient_square_integral b i).1 (P.coordinate_first_energy b i hi).1
  · intro t ht
    have hqlo : 0 ≤ q t := by dsimp [q]; linarith only [hi, P.upper t ht.le]
    have hqhi : q t ≤ angularEnergyWeight i^2 := by
      rw [angularEnergyWeight_sq]
      dsimp [q]
      linarith only [P.nonneg t]
    have h := mul_self_le_mul_self hqlo hqhi
    nlinarith only [h]
  · intro t ht
    rw [hqD, neg_sq]
    exact hV1 t ht
  · intro t ht
    rw [hqDD, neg_sq]
    exact hV2 t ht

#print axioms NativeHighPotential.coordinate_deriv
#print axioms NativeHighPotential.coordinate_first_energy
#print axioms NativeHighPotential.coordinate_higher_jet_energy
end Yamabe3.Analysis.Delaunay
