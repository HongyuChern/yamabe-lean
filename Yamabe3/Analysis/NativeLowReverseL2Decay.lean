import Yamabe3.Analysis.NativeLowReverseL2SameField
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! The same all-L2 low producer has actual C1 coefficients and decays
with its derivative at the exterior end. This follows from its constructed
bounded continuous inverse and derivative, not from a source representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)

def nativeLowReverseL2Coefficient (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (i : AngularIndex) (t : ℝ) : ℝ :=
  Real.exp (2*t)*lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb)
    (lowAngularOperatorBCF_norm_le v hv hb) F (-t) i

theorem nativeLowReverseL2Coefficient_hasDerivAt
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (i : AngularIndex) (t : ℝ) :
    HasDerivAt (nativeLowReverseL2Coefficient v hv hb F i)
      (Real.exp (2*t)*(2*lowL2ContinuousCLM (lowAngularOperatorBCF v hv hb)
        (lowAngularOperatorBCF_norm_le v hv hb) F (-t) i-
        lowL2DerivativeCLM (lowAngularOperatorBCF v hv hb)
          (lowAngularOperatorBCF_norm_le v hv hb) F (-t) i)) t := by
  let A := lowAngularOperatorBCF v hv hb
  let hA := lowAngularOperatorBCF_norm_le v hv hb
  let U := lowL2ContinuousCLM A hA F
  let D := lowL2DerivativeCLM A hA F
  have hdU := (lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).hasFDerivAt.comp_hasDerivAt (-t)
    (lowL2Continuous_hasDerivAt A hA F (-t))
  change HasDerivAt (fun s => U s i) (D (-t) i) ((-id : ℝ→ℝ) t) at hdU
  have hdUr : HasDerivAt (fun s => U (-s) i) (-D (-t) i) t := by
    simpa only [Function.comp_def,Pi.neg_apply,id_eq,mul_neg,mul_one] using
      hdU.comp t ((hasDerivAt_id t).neg)
  have he := ((Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)).mul hdUr
  apply he.congr_deriv
  change Real.exp (2*t)*(2*1)*U (-t) i+Real.exp (2*t)*(-D (-t) i)=
    Real.exp (2*t)*(2*U (-t) i-D (-t) i)
  ring

theorem nativeLowReverseL2Coefficient_bot
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (i : AngularIndex) :
    Tendsto (nativeLowReverseL2Coefficient v hv hb F i) atBot (𝓝 0) ∧
      Tendsto (deriv (nativeLowReverseL2Coefficient v hv hb F i)) atBot (𝓝 0) := by
  let A := lowAngularOperatorBCF v hv hb
  let hA := lowAngularOperatorBCF_norm_le v hv hb
  let U := lowL2ContinuousCLM A hA F
  let D := lowL2DerivativeCLM A hA F
  have hu (t : ℝ) : ‖U (-t) i‖≤‖U‖ :=
    (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (U (-t)) i).trans (U.norm_coe_le_norm _)
  have hd (t : ℝ) : ‖D (-t) i‖≤‖D‖ :=
    (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (D (-t)) i).trans (D.norm_coe_le_norm _)
  have he : Tendsto (fun t : ℝ => Real.exp (2*t)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).2 tendsto_id)
  constructor
  · have hbnd (t : ℝ) : ‖nativeLowReverseL2Coefficient v hv hb F i t‖≤‖U‖*Real.exp (2*t) := by
      change ‖Real.exp (2*t)*U (-t) i‖≤‖U‖*Real.exp (2*t)
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_comm ‖U‖]
      exact mul_le_mul_of_nonneg_left (hu t) (Real.exp_pos _).le
    apply squeeze_zero_norm' (Eventually.of_forall hbnd)
    simpa using he.const_mul ‖U‖
  · have hbnd (t : ℝ) : ‖deriv (nativeLowReverseL2Coefficient v hv hb F i) t‖≤
        (2*‖U‖+‖D‖)*Real.exp (2*t) := by
      rw [(nativeLowReverseL2Coefficient_hasDerivAt v hv hb F i t).deriv]
      change ‖Real.exp (2*t)*(2*U (-t) i-D (-t) i)‖≤_
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_comm (2*‖U‖+‖D‖)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc
        _≤‖(2:ℝ)*U (-t) i‖+‖D (-t) i‖ := norm_sub_le _ _
        _=2*‖U (-t) i‖+‖D (-t) i‖ := by rw [norm_mul];norm_num
        _≤2*‖U‖+‖D‖ := by nlinarith [hu t,hd t]
    apply squeeze_zero_norm' (Eventually.of_forall hbnd)
    simpa using he.const_mul (2*‖U‖+‖D‖)

#print axioms nativeLowReverseL2Coefficient_hasDerivAt
#print axioms nativeLowReverseL2Coefficient_bot
end Yamabe3.Analysis.SpherePolar
