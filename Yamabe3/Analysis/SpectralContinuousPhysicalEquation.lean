import Yamabe3.Analysis.SpectralL2OriginalIdentification
import Yamabe3.Analysis.NativeLowC2Coefficients

/-! The original continuous-source inverse has actual C2 physical
coordinates. Conjugation retains the exact source, potential and rate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralIntegralPotentialInverse_physical_coordinate_C2 {ι : Type*}
    (k : ι → ℝ) {k₀ κ : ℝ} (hk₀ : 0<k₀) (hk : ∀ i,k₀≤k i)
    (hδ : |(-2:ℝ)|<k₀) (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-2) s*|V (t-s)|)≤κ)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) :
    let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
    let q := fun t => Real.exp (-2*t)*U t i
    ContDiff ℝ 2 q ∧ ∀ t,deriv (deriv q) t-k i^2*q t=
      Real.exp (-2*t)*(F t i-V t*U t i) := by
  let U := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hV F
  have he := spectralIntegralPotentialInverse_coordinate_equation k hk₀ hk hδ hκ0 hκ1 V hV F i
  have hdd : Continuous (deriv (deriv (fun t => U t i))) := by
    rw [show deriv (deriv (fun t => U t i))=_ from funext he.2.2]
    exact (((continuous_const.mul he.2.1.continuous).add
      (continuous_const.mul he.1.continuous)).add
      (spectralCoordinate_continuous F i)).sub (V.continuous.mul he.1.continuous)
  have hC2 := contDiff_two_of_continuous_second_deriv he.1 he.2.1 hdd
  refine ⟨(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hC2,?_⟩
  intro t
  rw [exponential_conjugate_second_deriv_C2 he.1 he.2.1,he.2.2 t]
  dsimp only
  ring

#print axioms spectralIntegralPotentialInverse_physical_coordinate_C2
end Yamabe3.Analysis.Delaunay
