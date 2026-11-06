import Yamabe3.Analysis.L2BoundedScalarMultiplier
import Yamabe3.Analysis.NativeCollarLiftRepresentative
import Yamabe3.Analysis.Cylinder.NativeHalfEndCompactTesting

/-! The actual inverse-square potential is bounded on the fixed
entrance collar. No global boundedness near the puncture is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeCollarPotential_measurable (V : ℝ →ᵇ ℝ) : Measurable (nativeHalfEndPotentialCoefficient V) :=
  (V.continuous.measurable.comp (Real.measurable_log.comp measurable_norm).neg).div (measurable_norm.pow_const 2)

theorem nativeCollarPotential_bound (V : ℝ →ᵇ ℝ) {x : E} (hx : x∈nativePoissonEntranceCollar) :
    ‖nativeHalfEndPotentialCoefficient V x‖≤‖V‖*Real.exp 1 := by
  have hr := (nativeEntranceCollar_subset_shell hx).1
  have hs : Real.exp (-1)≤‖x‖^2 := by
    have h := pow_le_pow_left₀ (Real.exp_pos (-(1/2:ℝ))).le hr 2
    have he : Real.exp (-(1/2:ℝ))^2=Real.exp (-1) := by rw [pow_two,←Real.exp_add];norm_num
    rwa [he] at h
  have hx0 : x≠0 := cylinderShell_ne_zero (nativeEntranceCollar_subset_shell hx)
  rw [nativeHalfEndPotentialCoefficient,norm_div,norm_pow,norm_norm]
  have h1 := div_le_div_of_nonneg_left (norm_nonneg V) (Real.exp_pos (-1)) hs
  have h2 := div_le_div_of_nonneg_right (V.norm_coe_le_norm (-Real.log ‖x‖)) (sq_nonneg ‖x‖)
  apply h2.trans (h1.trans_eq ?_)
  rw [div_eq_mul_inv,←Real.exp_neg]
  norm_num

def nativeCollarPotentialMulCLM (V : ℝ →ᵇ ℝ) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) →L[ℝ] Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  l2ScalarMulCLM (nativeHalfEndPotentialCoefficient V) (nativeCollarPotential_measurable V).aestronglyMeasurable
    (‖V‖*Real.exp 1) (by positivity) (by
      filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
      exact nativeCollarPotential_bound V hx)

theorem nativeCollarPotentialMulCLM_ae (V : ℝ →ᵇ ℝ)
    (F : Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar)) :
    (nativeCollarPotentialMulCLM V F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => nativeHalfEndPotentialCoefficient V x*F x) := by
  exact l2ScalarMul_ae (nativeHalfEndPotentialCoefficient V)
    (nativeCollarPotential_measurable V).aestronglyMeasurable (‖V‖*Real.exp 1) (by positivity)
    (by filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
        exact nativeCollarPotential_bound V hx) F

#print axioms nativeCollarPotential_measurable
#print axioms nativeCollarPotential_bound
#print axioms nativeCollarPotentialMulCLM_ae
end Yamabe3.Analysis.SpherePolar
