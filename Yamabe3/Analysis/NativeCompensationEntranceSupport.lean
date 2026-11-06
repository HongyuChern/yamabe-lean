import Yamabe3.Analysis.NativeSupportedLowCompensationAllScale
import Yamabe3.Analysis.NativeScaledCutoffGeometry

/-! Literal compensation support is separated from the actual entrance
collar. All time shifts and physical dilations are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum

theorem bubbleCompensation_zero_of_ge_negative_half (i:AngularIndex) {t:ℝ} (ht:-(1/2:ℝ)≤ t):
    bubbleCompensation i t=0:=by
  have hz:bubbleCompensationCutoff t=0:=bubbleCompensationCutoff.zero_of_le_dist (by
    change (1/2:ℝ)≤ dist t (-1)
    rw [Real.dist_eq,abs_of_nonneg (by linarith)]
    linarith)
  simp only [bubbleCompensation,hz,zero_mul]

theorem nativeSupportedScaledCompensation_zero_entrance
    (b:ℝ) {τ:ℝ} (ht:0<τ) (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    {a:ℝ} (ha:0<a) (s:ℝ) (x:E) (hx:x∈euclideanDilatedDomain a nativePoissonEntranceCollar):
    nativeSupportedLowCompensationScaled b ht F d n s (Real.exp (s-Real.log a) • x)=0:=by
  have hx0:x≠0:=by
    intro hh
    have hn:a⁻¹ • x≠0:=hx.1
    exact hn (by rw [hh,smul_zero])
  let y:puncturedSpace:=⟨Real.exp (s-Real.log a) • x,by
    change Real.exp (s-Real.log a) • x≠0
    exact smul_ne_zero (Real.exp_pos _).ne' hx0⟩
  have hn:‖(y:E)‖=Real.exp s*‖a⁻¹ • x‖:=by
    change ‖Real.exp (s-Real.log a) • x‖=_
    rw [norm_smul,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (inv_pos.mpr ha).le,Real.exp_sub,Real.exp_log ha]
    field_simp
  have hlog:Real.log ‖(y:E)‖=s+Real.log ‖a⁻¹ • x‖:=by
    rw [hn,Real.log_mul (Real.exp_pos s).ne' (norm_pos_iff.mpr (smul_ne_zero (inv_ne_zero ha.ne') hx0)).ne',Real.log_exp]
  have harg:-(1/2:ℝ)≤ τ+(-Real.log ‖(y:E)‖+s):=by
    have hh:-(1/2:ℝ)< -Real.log ‖a⁻¹ • x‖:=hx.2.1
    rw [hlog]
    linarith
  have hzero(i:AngularIndex):bubbleCompensation i (τ+(-Real.log ‖(y:E)‖+s))=0:=
    bubbleCompensation_zero_of_ge_negative_half i harg
  change physicalForcing (finiteAngular nativeLowIndexFinset
    (fun i=>weightedTimeShift s (nativeSupportedLowCompensationCoefficients b ht F d n i))) (y:E)/8=0
  simp only [physicalForcing,cylinderLift_coe,puncturedCylinderLift,finiteAngular,
    weightedTimeShift,nativeSupportedLowCompensationCoefficients,cylinderCoordinates,hzero,mul_zero,zero_mul,
    Finset.sum_const_zero,zero_div]

#print axioms bubbleCompensation_zero_of_ge_negative_half
#print axioms nativeSupportedScaledCompensation_zero_entrance
end Yamabe3.Analysis.SpherePolar
