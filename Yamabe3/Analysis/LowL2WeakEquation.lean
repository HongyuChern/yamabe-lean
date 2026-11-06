import Yamabe3.Analysis.FutureL2WeakEquation

/-! The actual L2 future fixed point solves the original low-mode weak
ODE with the same source. No weak equation is assumed as input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem lowL2FutureInverse_weak_equation {ι : Type*}
    (A : ℝ →ᵇ (SpectralSpace ι →L[ℝ] SpectralSpace ι)) (hA : ‖A‖≤7/2)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (i : ι)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let U := lowL2FutureInverseCLM A hA F
    (∫ t : ℝ,deriv (deriv φ) t*U t i)+4*(∫ t : ℝ,deriv φ t*U t i)+
      4*(∫ t : ℝ,φ t*U t i)=
        (∫ t : ℝ,φ t*F t i)+(∫ t : ℝ,φ t*(A t (U t)) i) := by
  let U := lowL2FutureInverseCLM A hA F
  let G := F+l2BoundedOperatorActionCLM A U
  have h := doubleFutureL2_weak_equation (by norm_num : (0:ℝ)<2) G i φ hφ hc
  dsimp only at h
  have hfix : doubleFutureL2CLM 2 (by norm_num) G=U := lowL2FutureInverse_fixed A hA F
  rw [hfix] at h
  norm_num only [show (2*(2:ℝ))=4 by norm_num,show (2:ℝ)^2=4 by norm_num] at h
  have hp : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hc
  have he : (∫ t : ℝ,φ t*G t i)=
      (∫ t : ℝ,φ t*F t i)+(∫ t : ℝ,φ t*(A t (U t)) i) := by
    rw [←spectralL2TestCLM_apply i φ hp G]
    change spectralL2TestCLM i φ hp (F+l2BoundedOperatorActionCLM A U)=_
    rw [map_add,spectralL2TestCLM_apply,spectralL2TestCLM_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [l2BoundedOperatorAction_ae A U] with t ht
    exact congrArg (fun x : SpectralSpace ι => φ t*x i) ht
  exact h.trans he

theorem nativeLowL2FutureInverse_weak_equation (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t,0≤v t ∧ v t≤1)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) (i : AngularIndex)
    (hi : angularEigenvalue i < 6)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let U := nativeLowL2FutureInverseCLM v hv hb F
    (∫ t : ℝ,deriv (deriv φ) t*U t i)+4*(∫ t : ℝ,deriv φ t*U t i)+
      4*(∫ t : ℝ,φ t*U t i)=
        (∫ t : ℝ,φ t*F t i)+
        (∫ t : ℝ,φ t*((1/4+angularEigenvalue i-(15/4)*v t^4)*U t i)) := by
  have h := lowL2FutureInverse_weak_equation (lowAngularOperatorBCF v hv hb)
    (lowAngularOperatorBCF_norm_le v hv hb) F i φ hφ hc
  dsimp only at h
  dsimp only [nativeLowL2FutureInverseCLM]
  refine h.trans ?_
  apply congrArg (fun x : ℝ => (∫ t : ℝ,φ t*F t i)+x)
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change φ t*(lowAngularCoefficient v t i* _)=_
    rw [lowAngularCoefficient,if_pos hi]
    rfl

#print axioms lowL2FutureInverse_weak_equation
#print axioms nativeLowL2FutureInverse_weak_equation
end Yamabe3.Analysis.Delaunay
