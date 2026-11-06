import Yamabe3.Analysis.NativeWeakOperatorZeroLocality
import Yamabe3.Analysis.NativeOuterCutoffTestWindow

/-! The finite-window weak operator pairing is the WHOLE physical
pairing on exterior tests. The operator is genuinely zero off the
cutoff support by weak derivative locality; no volume a.e. identity is
restricted to a sphere or differentiated pointwise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem nativeOuterOperator_test_support_window
    {χ φ:E→ℝ} (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (hsφ:tsupport φ⊆{x:E|1<‖x‖}) {N:ℕ} {S:ℝ} (hcover:-S+1/2<(N:ℝ)/2):
    tsupport (fun x:E=>χ (Real.exp S • x))∩tsupport φ⊆nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0):=by
  intro x hx
  have hinner:1<‖x‖:=hsφ hx.2
  have houter:‖x‖<Real.exp ((1/8:ℝ)-S):=by
    have hh:=mem_ball_zero_iff.mp (nativeScaledCutoff_support hsχ S hx.1)
    rw [←Real.exp_add] at hh
    simpa only [sub_eq_add_neg] using hh
  have hn:0<‖x‖:=by linarith
  have hl:=Real.log_lt_log hn houter
  rw [Real.log_exp] at hl
  refine ⟨norm_pos_iff.mp hn,?_,?_⟩
  · linarith
  · have hh:=Real.log_nonneg hinner.le
    linarith

 theorem nativeOuterCompactOperator_window_to_global
    (g:RiemannianMetric 3 E) (a:ℝ) (V:ℝ→ᵇℝ) {u χ:E→ℝ}
    (hu:MemWkp 2 2 u univ) (S:ℝ)
    (hz:∀x:E,χ (Real.exp S • x)=0→u x=0)
    (hsχ:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (N:ℕ) (hcover:-S+1/2<(N:ℝ)/2)
    (φ:E→ℝ) (hsφ:tsupport φ⊆{x:E|1<‖x‖}):
    (∫x in nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0),
      (nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)*φ x)=
      ∫x:E,(nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)*φ x:=by
  let χp:E→ℝ:=fun x=>χ (Real.exp S • x)
  let U:Set E:=(tsupport χp)ᶜ
  have hU:IsOpen U:=(isClosed_tsupport χp).isOpen_compl
  have hu0:EqOn u (fun _=>0) U:=by
    intro x hx
    have hp:χp x=0:=image_eq_zero_of_notMem_tsupport hx
    exact hz x hp
  have hzero:=nativeGlobalFullBCF_zero_on_open hu hU hu0 g a V
  have hfull:∀ᵐx:E∂volume,x∈U→
      (nativeWeakRescaledDelaunayJacobian univ g a (fun _=>0) 0 u x-
        g.pullbackVolumeDensity id (a • x)*nativeHalfEndPotentialCoefficient V x*u x)=0:=
    (ae_restrict_iff' hU.measurableSet).mp hzero
  rw [←integral_indicator (nativePolarTimeWindow_measurable measurableSet_Ioc)]
  apply integral_congr_ae
  filter_upwards [hfull] with x hx
  by_cases hxW:x∈nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0)
  · rw [indicator_of_mem hxW]
  · rw [indicator_of_notMem hxW]
    by_cases hφ:φ x=0
    · rw [hφ,mul_zero]
    · have hxφ:x∈tsupport φ:=subset_closure (show x∈Function.support φ from hφ)
      have hxU:x∈U:=by
        intro hxχ
        exact hxW (nativeOuterOperator_test_support_window hsχ hsφ hcover ⟨hxχ,hxφ⟩)
      rw [hx hxU,zero_mul]

#print axioms nativeOuterOperator_test_support_window
#print axioms nativeOuterCompactOperator_window_to_global
end Yamabe3.Analysis.SpherePolar
