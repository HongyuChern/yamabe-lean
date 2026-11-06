import Yamabe3.Analysis.WeightedTimeShiftEnergy
import Yamabe3.Analysis.NativePoissonExteriorExtension

/-! Weighted shifts of the actual reversed-time exterior Poisson curve.
Exact whole-line energies give exp(4s), with no restriction on the shift.
The resulting estimate is uniform on the exterior half-end s <= 0. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def nativeExteriorShiftedCoefficient (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) : ℝ → ℝ :=
  weightedTimeShift s (nativePoissonExteriorExtension P b i)

def nativeExteriorShiftedEnergy (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) : ℝ :=
  let z := nativeExteriorShiftedCoefficient P b s i
  let w := angularEnergyWeight i
  w^4*(∫ t : ℝ,z t^2)+w^2*(∫ t : ℝ,deriv z t^2)+(∫ t : ℝ,deriv (deriv z) t^2)

 theorem nativeExteriorShiftedCoefficient_C2 (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    ContDiff ℝ 2 (nativeExteriorShiftedCoefficient P b s i) :=
  weightedTimeShift_C2 s (P.exteriorExtension_C2 b i)

 theorem nativeExteriorShiftedEnergy_eq (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    nativeExteriorShiftedEnergy P b s i=Real.exp (4*s)*nativePoissonExteriorSecondEnergy P b i := by
  unfold nativeExteriorShiftedEnergy nativeExteriorShiftedCoefficient nativePoissonExteriorSecondEnergy
  dsimp only
  rw [weightedTimeShift_second s (P.exteriorExtension_C2 b i),
    weightedTimeShift_deriv s ((P.exteriorExtension_C2 b i).differentiable (by norm_num))]
  rw [weightedTimeShift_square_integral,weightedTimeShift_square_integral,weightedTimeShift_square_integral]
  ring

 theorem nativeExteriorShiftedEnergy_spectral_bound (P : NativeHighPotential)
    (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    let z := nativeExteriorShiftedCoefficient P b s i
    Integrable (fun t => z t^2) ∧ Integrable (fun t => deriv z t^2) ∧
      Integrable (fun t => deriv (deriv z) t^2) ∧
      nativeExteriorShiftedEnergy P b s i ≤
        (4000*Real.exp (4*s)*(4+P.derivativeBound))*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  have hI := P.exterior_energy_spectral_bound b i
  have hC := P.exteriorExtension_C2 b i
  dsimp only
  refine ⟨weightedTimeShift_square_integrable s hI.1,?_,?_,?_⟩
  · change Integrable (fun t => deriv (weightedTimeShift s (nativePoissonExteriorExtension P b i)) t^2)
    rw [weightedTimeShift_deriv s (hC.differentiable (by norm_num))]
    exact weightedTimeShift_square_integrable s hI.2.1
  · change Integrable (fun t => deriv (deriv (weightedTimeShift s (nativePoissonExteriorExtension P b i))) t^2)
    rw [weightedTimeShift_second s hC]
    exact weightedTimeShift_square_integrable s hI.2.2.1
  · rw [nativeExteriorShiftedEnergy_eq]
    exact (mul_le_mul_of_nonneg_left hI.2.2.2 (Real.exp_pos (4*s)).le).trans_eq (by ring)

#print axioms nativeExteriorShiftedCoefficient_C2
#print axioms nativeExteriorShiftedEnergy_eq
#print axioms nativeExteriorShiftedEnergy_spectral_bound
end Yamabe3.Analysis.Delaunay
