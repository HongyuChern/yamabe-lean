import Yamabe3.Analysis.NativeActualIncomingLocalEquation
import Yamabe3.Analysis.DensityCutoffCommutatorIdentity
import Yamabe3.Analysis.DensityCutoffCommutatorScaling

/-! The exact unit-coordinate operator of the actual compact core.
Its negative commutator identity and support use the actual homogeneous
field equation, core plateau, and support; no source identity is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def nativeCoreUnitOperator (gE:RiemannianMetric 3 E) (a:ℝ) (χ F:E→ℝ) (x:E):ℝ:=
  principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) (fun y=>χ y*F y) x+
    a^2*nativePotentialDensity gE (a • x)*(χ x*F x)

theorem nativeCoreUnitOperator_eq_negative_commutator
    (gE:RiemannianMetric 3 E) (a:ℝ) (χ F:E→ℝ)
    (hχ:ContDiff ℝ ∞ χ) (hF:ContDiff ℝ ∞ F) (hs:tsupport χ⊆ball (0:E) 3)
    (hzero:∀x∈closedBall (0:E) 4,
      principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
        a^2*nativePotentialDensity gE (a • x)*F x=0) (x:E):
    nativeCoreUnitOperator gE a χ F x=
      -densityCutoffCommutator (fun y=>nativeDivergenceMatrix gE (a • y)) χ F x:=by
  have he:=densityCutoffCommutator_eq_principal_difference (fun y=>nativeDivergenceMatrix gE (a • y))
    (fun i j=>(contDiff_nativeDivergenceMatrix gE i j).comp (contDiff_id.const_smul a))
    isOpen_univ (hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn (mem_univ x)
  have hz:χ x*(principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
      a^2*nativePotentialDensity gE (a • x)*F x)=0:=by
    by_cases hx:x∈closedBall (0:E) 4
    · rw [hzero x hx,mul_zero]
    · have hn:x∉tsupport χ:=fun h=>hx (ball_subset_closedBall ((ball_subset_ball (by norm_num:(3:ℝ)≤4)) (hs h)))
      rw [image_eq_zero_of_notMem_tsupport hn,zero_mul]
  unfold nativeCoreUnitOperator
  linarith only [he,hz]

theorem native_core_transition_subset_incoming :
    {x:E|2≤‖x‖ ∧‖x‖≤3}⊆(fun x:E=>(1/2:ℝ) • x) ⁻¹' nativePoissonEntranceCollar:=by
  intro x hx
  apply (nativePolarTimeWindow_norm (1/2) _).mpr
  rw [norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ)≤1/2)]
  have hlo:Real.exp (-(1/2:ℝ))<1:=Real.exp_lt_one_iff.mpr (by norm_num)
  have hhi:(3/2:ℝ)<Real.exp (1/2:ℝ):=by
    have h:=Real.add_one_lt_exp (by norm_num:(1/2:ℝ)≠0)
    linarith
  exact ⟨by nlinarith [hx.1],by nlinarith [hx.2]⟩

theorem nativeCoreUnitOperator_zero_off_incoming
    (gE:RiemannianMetric 3 E) (a:ℝ) (χ F:E→ℝ)
    (hs:tsupport χ⊆ball (0:E) 3)
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))
    (hzero:∀x∈closedBall (0:E) 4,
      principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
        a^2*nativePotentialDensity gE (a • x)*F x=0)
    {x:E} (hx:x∉(fun x:E=>(1/2:ℝ) • x) ⁻¹' nativePoissonEntranceCollar):
    nativeCoreUnitOperator gE a χ F x=0:=by
  have hn:¬(2≤‖x‖ ∧‖x‖≤3):=fun h=>hx (native_core_transition_subset_incoming h)
  by_cases h2:‖x‖<2
  · have hx2:x∈closedBall (0:E) 2:=mem_closedBall_zero_iff.mpr h2.le
    have hg:(fun y=>χ y*F y)=ᶠ[𝓝 x]F:=by
      filter_upwards [h1 x hx2] with y hy
      rw [hy,one_mul]
    unfold nativeCoreUnitOperator
    rw [principalSource_eq_of_eventuallyEq _ hg,(h1 x hx2).self_of_nhds,one_mul]
    exact hzero x ((closedBall_subset_closedBall (by norm_num:(2:ℝ)≤4)) hx2)
  · have h3:3<‖x‖:=lt_of_not_ge (fun h=>hn ⟨le_of_not_gt h2,h⟩)
    have hnot:x∉tsupport χ:=fun h=>not_le_of_gt h3 (le_of_lt (mem_ball_zero_iff.mp (hs h)))
    have hg:(fun y=>χ y*F y)=ᶠ[𝓝 x](fun _=>0):=by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
      simp only [hy,Pi.zero_apply,zero_mul]
    unfold nativeCoreUnitOperator
    rw [principalSource_eq_of_eventuallyEq _ hg,image_eq_zero_of_notMem_tsupport hnot,zero_mul,mul_zero]
    have hf(j:Fin 3):partialDeriv j (fun _:E=>0)=(fun _:E=>0):=by
      funext y
      simp only [partialDeriv,fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.zero_apply]
    have hflux(i:Fin 3):matrixFlux (fun y=>nativeDivergenceMatrix gE (a • y))
        (fun j=>partialDeriv j (fun _:E=>0)) i=(fun _:E=>0):=by
      funext y
      simp only [matrixFlux,hf,mul_zero,Finset.sum_const_zero]
    simp only [principalSource]
    simp only [hflux]
    simp only [hf,Pi.zero_apply,Finset.sum_const_zero,neg_zero,add_zero]

#print axioms nativeCoreUnitOperator_eq_negative_commutator
#print axioms native_core_transition_subset_incoming
#print axioms nativeCoreUnitOperator_zero_off_incoming
end Yamabe3.Analysis.SpherePolar
