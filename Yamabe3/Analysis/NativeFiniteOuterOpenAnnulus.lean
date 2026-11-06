import Yamabe3.Analysis.NativeScaledCutoffGeometry
import Yamabe3.Analysis.NativeOuterWindowReconstruction

/-! The actual open finite exterior annulus in physical chart units.
Its relation to the unit log window and chart fit is proved, not added
as a source or PDE assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

 def nativeFiniteOuterOpenAnnulus (a:ℝ) (N:ℕ):Set E:=
    {x:E|a<‖x‖ ∧ ‖x‖<a*Real.exp ((N:ℝ)/2)}

 theorem nativeFiniteOuterOpenAnnulus_open (a:ℝ) (N:ℕ):IsOpen (nativeFiniteOuterOpenAnnulus a N):=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

 theorem nativeFiniteOuterOpenAnnulus_chart_fit
    {a R:ℝ} (ha:0<a) (N:ℕ) (hfit:a*Real.exp ((N:ℝ)/2+1)≤R):
    nativeFiniteOuterOpenAnnulus a N⊆closedBall (0:E) R:=by
  intro x hx
  rw [mem_closedBall_zero_iff]
  exact hx.2.le.trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith:(N:ℝ)/2≤(N:ℝ)/2+1)) ha.le).trans hfit)

 theorem nativeFiniteOuterOpenAnnulus_unit_window
    {a:ℝ} (ha:0<a) (N:ℕ) {x:E} (hx:x∈nativeFiniteOuterOpenAnnulus a N):
    a⁻¹ • x∈nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0) ∧ 1<‖a⁻¹ • x‖:=by
  have hnorm:a*‖a⁻¹ • x‖=‖x‖:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
  have hinner:1<‖a⁻¹ • x‖:=by nlinarith only [hx.1,hnorm,ha]
  have houter:‖a⁻¹ • x‖<Real.exp ((N:ℝ)/2):=by nlinarith only [hx.2,hnorm,ha]
  have hpos:0<‖a⁻¹ • x‖:=by linarith
  have hlN:=Real.log_lt_log hpos houter
  rw [Real.log_exp] at hlN
  have hl0:=Real.log_pos hinner
  exact ⟨⟨norm_pos_iff.mp hpos,by linarith,by linarith⟩,hinner⟩

#print axioms nativeFiniteOuterOpenAnnulus_open
#print axioms nativeFiniteOuterOpenAnnulus_chart_fit
#print axioms nativeFiniteOuterOpenAnnulus_unit_window
end Yamabe3.Analysis.SpherePolar
