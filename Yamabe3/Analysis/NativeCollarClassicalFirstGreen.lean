import Yamabe3.Analysis.NativeEuclideanSphereFirstGreen
import Yamabe3.Analysis.NativeCollarClassicalGreen

/-! First-order Green identity with the actual value trace. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.EuclideanSphereTrace
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def nativeCollarFirstGreenIntegrand (j : Fin 3) (u ψ : E → ℝ) (x : E) : ℝ :=
  partialDeriv j ψ x*u x+ψ x*partialDeriv j u x

theorem native_collar_classical_first_green (u : nativeC2OffZero) (ψ : E → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (j : Fin 3) :
    (∫x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarFirstGreenIntegrand j u.val ψ x)=
      -(∫θ : S,ψ (θ:E)*u.val (θ:E)*(θ:E) j ∂angularVolume) := by
  obtain ⟨F,hF,-,hg⟩ := exists_compact_C2_extension_near_compact isClosed_singleton.isOpen_compl
    (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) u.property
  have hm (x : E) : partialDeriv j (fun x => ψ x*F x) x=nativeCollarFirstGreenIntegrand j F ψ x := by
    simp only [nativeCollarFirstGreenIntegrand,partialDeriv]
    rw [fderiv_fun_mul (hψ.differentiable (by norm_num)).differentiableAt (hF.differentiable (by norm_num)).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have h := native_exterior_partial_integral (hψ.mul hF) hc.mul_right j
  simp_rw [hm] at h
  have he : (∫x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarFirstGreenIntegrand j F ψ x)=
      ∫x in {y : E | 1<‖y‖},nativeCollarFirstGreenIntegrand j F ψ x := by
    have hΩ : MeasurableSet nativePoissonEntranceCollar := (nativePolarTimeWindow_open (1/2)).measurableSet
    rw [←Measure.restrict_restrict hΩ]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x∉tsupport ψ := fun h => hx (hs h)
    have hd : partialDeriv j ψ x=0 := by
      unfold partialDeriv
      rw [fderiv_of_notMem_tsupport ℝ hn]
      rfl
    simp only [nativeCollarFirstGreenIntegrand,hd,image_eq_zero_of_notMem_tsupport hn,zero_mul,add_zero]
  calc
    _ = ∫x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarFirstGreenIntegrand j F ψ x := by
      apply setIntegral_congr_fun ((nativePolarTimeWindow_open (1/2)).measurableSet.inter
        (isOpen_lt continuous_const continuous_norm).measurableSet)
      intro x hx
      have hgx := hg x (subset_closure hx.1)
      have hd := congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) hgx.fderiv_eq
      simp only [nativeCollarFirstGreenIntegrand,partialDeriv,hgx.eq_of_nhds,hd]
    _ = _ := by
      rw [he,h]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun θ => by
        dsimp only
        rw [(hg (θ:E) (subset_closure (native_unit_sphere_mem_collar θ))).eq_of_nhds]

#print axioms native_collar_classical_first_green
end Yamabe3.Analysis.SpherePolar
