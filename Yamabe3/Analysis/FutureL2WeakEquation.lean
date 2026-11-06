import Yamabe3.Analysis.FutureL2Original
import Yamabe3.Analysis.SpectralL2TestPairing
import Yamabe3.Analysis.L2ContinuousSourceDense
import Yamabe3.Analysis.TimeTestC2Equation

/-! The actual double future L2 integral satisfies its second-order weak
ODE, by density from the original twice differentiable integral. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

 theorem doubleFuture_observable_equation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {k : ℝ} (hk : 0<k) (F : ℝ →ᵇ H) (L : H →L[ℝ] ℝ) :
    let y := fun t => L (banachDoubleFutureResolvent k hk F t)
    Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
      ∀ t,deriv (deriv y) t=(2*k)*deriv y t-k^2*y t+L (F t) := by
  dsimp only
  let u := fun t => banachDoubleFutureResolvent k hk F t
  have h := banachDoubleFutureResolvent_equation hk F
  dsimp only at h
  have hd (t : ℝ) : HasDerivAt (fun s => L (u s)) (L (deriv u t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (h.1 t).hasDerivAt
  have he : deriv (fun s => L (u s))=(fun t => L (deriv u t)) := funext fun t => (hd t).deriv
  have hd2 (t : ℝ) : HasDerivAt (fun s => L (deriv u s)) (L (deriv (deriv u) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (h.2.1 t).hasDerivAt
  refine ⟨fun t => (hd t).differentiableAt,?_,fun t => ?_⟩
  · rw [he]
    exact fun t => (hd2 t).differentiableAt
  · rw [he,(hd2 t).deriv,h.2.2.2 t]
    simp only [map_add,map_sub,map_smul,smul_eq_mul]
    rfl

 theorem doubleFutureL2_weak_equation {ι : Type*} {k : ℝ} (hk : 0<k)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (i : ι)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let U := doubleFutureL2CLM k hk F
    (∫ t : ℝ,deriv (deriv φ) t*U t i)+(2*k)*(∫ t : ℝ,deriv φ t*U t i)+
      k^2*(∫ t : ℝ,φ t*U t i)=∫ t : ℝ,φ t*F t i := by
  let R := doubleFutureL2CLM (H := SpectralSpace ι) k hk
  have hφ1 := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ2 := (contDiff_infty_iff_deriv.mp hφ1).2
  have hp0 : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hc
  have hp1 : MemLp (deriv φ) 2 := hφ1.continuous.memLp_of_hasCompactSupport hc.deriv
  have hp2 : MemLp (deriv (deriv φ)) 2 := hφ2.continuous.memLp_of_hasCompactSupport hc.deriv.deriv
  let T0 := spectralL2TestCLM i φ hp0
  let T1 := spectralL2TestCLM i (deriv φ) hp1
  let T2 := spectralL2TestCLM i (deriv (deriv φ)) hp2
  let L := T2.comp R+(2*k) • T1.comp R+k^2 • T0.comp R
  have he : (L : Lp (SpectralSpace ι) 2 (volume : Measure ℝ) → ℝ)=T0 := by
    apply continuous_L2_eq_of_boundedContinuous_sources L.continuous T0.continuous
    intro H hH
    have ha := doubleFutureL2_agrees_original hk H hH
    let W := banachDoubleFutureResolvent k hk H
    change (R (hH.toLp H) : ℝ → SpectralSpace ι)=ᵐ[volume]W at ha
    have ho := doubleFuture_observable_equation hk H (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i)
    change Differentiable ℝ (fun t => W t i) ∧ Differentiable ℝ (deriv (fun t => W t i)) ∧
      (∀ t,deriv (deriv (fun s => W s i)) t=(2*k)*deriv (fun s => W s i) t-k^2*(W t i)+H t i) at ho
    change T2 (R (hH.toLp H))+(2*k)*T1 (R (hH.toLp H))+k^2*T0 (R (hH.toLp H))=T0 (hH.toLp H)
    dsimp only [T0,T1,T2]
    rw [spectralL2TestCLM_apply_ae i _ hp2 _ W ha,
      spectralL2TestCLM_apply_ae i _ hp1 _ W ha,
      spectralL2TestCLM_apply_ae i _ hp0 _ W ha,
      spectralL2TestCLM_apply_ae i _ hp0 _ H hH.coeFn_toLp]
    have hode (t : ℝ) : deriv (deriv (fun s => W s i)) t=
        (2*k)*deriv (fun s => W s i) t+(-k^2)*(W t i)+(H t i)-(0:ℝ)*(W t i) := by
      simpa only [zero_mul,sub_zero,neg_mul,sub_eq_add_neg,neg_zero,add_zero] using ho.2.2 t
    have htest := second_order_compact_time_test_differentiable hφ hc ho.1 ho.2.1
      (continuous_const (y := (0:ℝ))) (spectralCoordinate_continuous H i) hode
    simpa only [mul_zero,zero_mul,integral_zero,add_zero,neg_mul,sub_neg_eq_add] using htest
  have hh := congrFun he F
  change T2 (R F)+(2*k)*T1 (R F)+k^2*T0 (R F)=T0 F at hh
  simpa only [T0,T1,T2,spectralL2TestCLM_apply,R] using hh

#print axioms doubleFuture_observable_equation
#print axioms doubleFutureL2_weak_equation
end Yamabe3.Analysis.Delaunay
