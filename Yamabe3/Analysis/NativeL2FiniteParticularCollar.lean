import Yamabe3.Analysis.NativeFiniteResidualCollar
import Yamabe3.Analysis.SpectralContinuousPhysicalEquation
import Yamabe3.Analysis.SpectralL2OriginalSquareBound
import Yamabe3.Analysis.SpectralL2EntranceRegularity

/-! Uniform physical value/Laplacian collar estimates for the actual
same-source continuous L2 particular solution. Finite truncations contain
only genuine high modes, so no auxiliary low rate is mistaken for the
round-sphere Laplacian. Constants are independent of the truncation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)

def nativeL2FiniteParticular (F : ℝ →ᵇ SpectralSpace AngularIndex) (s : Finset AngularIndex) : E → ℝ :=
  finitePhysical s (fun i t => Real.exp (-2*t)*
    spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
      (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F t i)

include hplus in
theorem nativeL2FiniteParticular_collar_energy
    (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2)
    (s : Finset AngularIndex) (hs : ∀ i ∈ s,6≤angularEigenvalue i) :
    let u := nativeL2FiniteParticular hκ0 hκ1 V hminus F s
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    let B := (1-κ)⁻¹*(4/9)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
      IntegrableOn (fun x => u x^2) O ∧
      IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        (Real.exp 6*B^2+Real.exp 2*(1+‖V‖*B)^2)*‖hF.toLp F‖^2 := by
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num : (0:ℝ)<5/2)
    nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F
  let G := fun t => F t-V t • U t
  have ho (i : AngularIndex) := spectralIntegralPotentialInverse_physical_coordinate_C2 nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus F i
  obtain ⟨hU,hG,hUn,hGn⟩ := spectralIntegralPotentialInverse_actual_square_bounds nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa only [neg_neg] using hplus) F hF
  change MemLp U 2 at hU
  change MemLp G 2 at hG
  have he := native_finite_conjugated_collar_energy s (fun i t => U t i) (fun i t => G t i)
    (fun i _ => (ho i).1) (fun i hi t => by
      change deriv (deriv (fun t => Real.exp (-2*t)*U t i)) t-
        (angularEigenvalue i+1/4)*(Real.exp (-2*t)*U t i)=Real.exp (-2*t)*(G t i)
      rw [←show nativeAngularRate i^2=angularEigenvalue i+1/4 by
        rw [nativeAngularRate_sq,max_eq_right (hs i hi)]]
      exact (ho i).2 t)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hU).integrable_sq)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hG).integrable_sq)
  refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.trans ?_⟩
  have hu := (spectralL2_finite_coordinate_integral_bound U hU s).trans hUn
  have hg := (spectralL2_finite_coordinate_integral_bound G hG s).trans hGn
  have hb := add_le_add (mul_le_mul_of_nonneg_left hu (Real.exp_pos 6).le)
    (mul_le_mul_of_nonneg_left hg (Real.exp_pos 2).le)
  exact hb.trans_eq (by norm_num;ring)

#print axioms nativeL2FiniteParticular_collar_energy
end Yamabe3.Analysis.SpherePolar
