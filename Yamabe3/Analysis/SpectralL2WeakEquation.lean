import Yamabe3.Analysis.SpectralL2TestPairing
import Yamabe3.Analysis.L2ContinuousSourceDense
import Yamabe3.Analysis.TimeTestC2Equation

/-! The actual L2 inverse solves the transposed conjugated equation for
every compact smooth time test, in every spectral coordinate. The proof
extends the established continuous-source ODE by genuine L2 density and
continuous integral pairings, preserving the same source and potential. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2IntegralPotentialInverse_weak_equation {ι : Type*} (k : ι → ℝ) {k₀ δ κ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀ i,k₀ ≤ k i) (hδ : |δ|<k₀) (hκ0 : 0 ≤ κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ δ s * |V (t-s)|) ≤ κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-δ) s * |V (t-s)|) ≤ κ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (i : ι)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let U := spectralL2IntegralPotentialInverse k hk₀ hk hδ V F
    (∫ t : ℝ,deriv (deriv φ) t*U t i)+(-2*δ)*(∫ t : ℝ,deriv φ t*U t i)-
      (k i^2-δ^2)*(∫ t : ℝ,φ t*U t i)+(∫ t : ℝ,φ t*V t*U t i)=
        ∫ t : ℝ,φ t*F t i := by
  let R := spectralL2IntegralPotentialInverse k hk₀ hk hδ V
  have hφ1 := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ2 := (contDiff_infty_iff_deriv.mp hφ1).2
  have hp0 : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hc
  have hp1 : MemLp (deriv φ) 2 := hφ1.continuous.memLp_of_hasCompactSupport hc.deriv
  have hp2 : MemLp (deriv (deriv φ)) 2 := hφ2.continuous.memLp_of_hasCompactSupport hc.deriv.deriv
  have hpV : MemLp (fun t => φ t*V t) 2 :=
    (hφ.continuous.mul V.continuous).memLp_of_hasCompactSupport hc.mul_right
  let T0 := spectralL2TestCLM i φ hp0
  let T1 := spectralL2TestCLM i (deriv φ) hp1
  let T2 := spectralL2TestCLM i (deriv (deriv φ)) hp2
  let TV := spectralL2TestCLM i (fun t => φ t*V t) hpV
  let L := T2.comp R+(-2*δ) • T1.comp R-(k i^2-δ^2) • T0.comp R+TV.comp R
  have he : (L : Lp (SpectralSpace ι) 2 (volume : Measure ℝ) → ℝ)=T0 := by
    apply continuous_L2_eq_of_boundedContinuous_sources L.continuous T0.continuous
    intro H hH
    have ha := spectralL2IntegralPotentialInverse_agrees_original k hk₀ hk hδ hκ0 hκ1 V hminus hplus H hH
    let W := spectralIntegralPotentialInverse k hk₀ hk hδ hκ0 hκ1 V hminus H
    change (R (hH.toLp H) : ℝ → SpectralSpace ι)=ᵐ[volume] W at ha
    have ho := spectralIntegralPotentialInverse_coordinate_equation k hk₀ hk hδ hκ0 hκ1 V hminus H i
    change T2 (R (hH.toLp H))+(-2*δ)*T1 (R (hH.toLp H))-
      (k i^2-δ^2)*T0 (R (hH.toLp H))+TV (R (hH.toLp H))=T0 (hH.toLp H)
    dsimp only [T0,T1,T2,TV]
    rw [spectralL2TestCLM_apply_ae i _ hp2 _ W ha,
      spectralL2TestCLM_apply_ae i _ hp1 _ W ha,
      spectralL2TestCLM_apply_ae i _ hp0 _ W ha,
      spectralL2TestCLM_apply_ae i _ hpV _ W ha,
      spectralL2TestCLM_apply_ae i _ hp0 _ H hH.coeFn_toLp]
    exact second_order_compact_time_test_differentiable hφ hc ho.1 ho.2.1
      V.continuous (spectralCoordinate_continuous H i) ho.2.2
  have hh := congrFun he F
  change T2 (R F)+(-2*δ)*T1 (R F)-(k i^2-δ^2)*T0 (R F)+TV (R F)=T0 F at hh
  simpa only [T0,T1,T2,TV,spectralL2TestCLM_apply,R] using hh

#print axioms spectralL2IntegralPotentialInverse_weak_equation
end Yamabe3.Analysis.Delaunay
