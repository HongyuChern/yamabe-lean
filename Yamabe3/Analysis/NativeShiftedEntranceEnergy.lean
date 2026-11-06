import Yamabe3.Analysis.WeightedTimeShiftEnergy

/-! The actual entrance reflection supplies uniformly controlled physical
collars throughout the finite entrance interval. It is the same reflected
curve, shifted with the original weight; no PDE is asserted at negative time. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

def nativeShiftedEntranceCoefficient (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) : ℝ → ℝ :=
  weightedTimeShift s (nativePoissonEntranceExtension P b i)

def nativeShiftedEntranceEnergy (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) : ℝ :=
  let z := nativeShiftedEntranceCoefficient P b s i
  let w := angularEnergyWeight i
  w^4*(∫ t : ℝ,z t^2)+w^2*(∫ t : ℝ,deriv z t^2)+(∫ t : ℝ,deriv (deriv z) t^2)

 theorem nativeShiftedEntranceCoefficient_C2 (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    ContDiff ℝ 2 (nativeShiftedEntranceCoefficient P b s i) :=
  weightedTimeShift_C2 s (P.entranceExtension_C2 b i)

 theorem nativeShiftedEntranceEnergy_eq (P : NativeHighPotential) (b : AngularH1) (s : ℝ) (i : AngularIndex) :
    nativeShiftedEntranceEnergy P b s i=Real.exp (4*s)*nativePoissonReflectedSecondEnergy P b i := by
  unfold nativeShiftedEntranceEnergy nativeShiftedEntranceCoefficient nativePoissonReflectedSecondEnergy
  dsimp only
  rw [weightedTimeShift_second s (P.entranceExtension_C2 b i),
    weightedTimeShift_deriv s ((P.entranceExtension_C2 b i).differentiable (by norm_num))]
  rw [weightedTimeShift_square_integral,weightedTimeShift_square_integral,weightedTimeShift_square_integral]
  ring

 theorem nativeShiftedEntranceEnergy_spectral_bound (P : NativeHighPotential)
    (b : AngularH1) (s : ℝ) (hs : s ≤ 2) (i : AngularIndex) :
    let z := nativeShiftedEntranceCoefficient P b s i
    Integrable (fun t => z t^2) ∧ Integrable (fun t => deriv z t^2) ∧
      Integrable (fun t => deriv (deriv z) t^2) ∧
      nativeShiftedEntranceEnergy P b s i ≤
        (4000*Real.exp 8*(4+P.derivativeBound))*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  have hI := P.reflected_energy_spectral_bound b i
  have hC := P.entranceExtension_C2 b i
  dsimp only
  refine ⟨weightedTimeShift_square_integrable s hI.1,?_,?_,?_⟩
  · change Integrable (fun t => deriv (weightedTimeShift s (nativePoissonEntranceExtension P b i)) t^2)
    rw [weightedTimeShift_deriv s (hC.differentiable (by norm_num))]
    exact weightedTimeShift_square_integrable s hI.2.1
  · change Integrable (fun t => deriv (deriv (weightedTimeShift s (nativePoissonEntranceExtension P b i))) t^2)
    rw [weightedTimeShift_second s hC]
    exact weightedTimeShift_square_integrable s hI.2.2.1
  · rw [nativeShiftedEntranceEnergy_eq]
    have hn : 0 ≤ nativePoissonReflectedSecondEnergy P b i := by
      unfold nativePoissonReflectedSecondEnergy
      positivity
    calc
      _ ≤ Real.exp 8*nativePoissonReflectedSecondEnergy P b i :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hn
      _ ≤ Real.exp 8*((4000*(4+P.derivativeBound))*nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) :=
        mul_le_mul_of_nonneg_left hI.2.2.2 (Real.exp_pos _).le
      _ = _ := by ring

#print axioms nativeShiftedEntranceCoefficient_C2
#print axioms nativeShiftedEntranceEnergy_eq
#print axioms nativeShiftedEntranceEnergy_spectral_bound
end Yamabe3.Analysis.Delaunay
