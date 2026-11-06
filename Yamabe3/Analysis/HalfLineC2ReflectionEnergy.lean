import Yamabe3.Analysis.HalfLineC2Reflection
import Yamabe3.Analysis.HalfLineReflectionEnergy

/-! Uniform L² bounds for the value and both genuine derivatives of
the entrance-preserving extension. The constant is numerical and
independent of the field, frequency and boundary datum. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem halfLineC2Extension_energy
    {f df ddf : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (df t) (Ici 0) t)
    (hdf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt df (ddf t) (Ici 0) t)
    (hddf : ContinuousOn ddf (Ici 0))
    (hfI : IntegrableOn (fun t => f t^2) (Ioi 0))
    (hdfI : IntegrableOn (fun t => df t^2) (Ioi 0))
    (hddfI : IntegrableOn (fun t => ddf t^2) (Ioi 0)) :
    let u := halfLineC2Extension f
    (Integrable (fun t => u t^2) ∧ (∫ t : ℝ,u t^2) ≤ 4000*(∫ t : ℝ in Ioi 0,f t^2)) ∧
    (Integrable (fun t => deriv u t^2) ∧ (∫ t : ℝ,deriv u t^2) ≤ 4000*(∫ t : ℝ in Ioi 0,df t^2)) ∧
    (Integrable (fun t => deriv (deriv u) t^2) ∧
      (∫ t : ℝ,deriv (deriv u) t^2) ≤ 4000*(∫ t : ℝ in Ioi 0,ddf t^2)) := by
  let r := halfLineC2Rates
  let c := halfLineC2Coeffs
  let c1 := fun j => -r j*c j
  let c2 := fun j => -r j*c1 j
  have hr : ∀ j, 0 < r j := by intro j; fin_cases j <;> norm_num [r,halfLineC2Rates]
  have hc : ∑ j,c j = 1 := by norm_num [c,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hc1 : ∑ j,c1 j = 1 := by norm_num [c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hc2 : ∑ j,c2 j = 1 := by norm_num [c2,c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hD := halfLineReflection_hasDeriv r c hr hc hc1 hf
  have hDD := halfLineReflection_hasDeriv r c1 hr hc1 hc2 hdf
  have heD : deriv (halfLineC2Extension f) = halfLineReflection r c1 df :=
    funext fun t => (hD t).deriv
  have heDD : deriv (deriv (halfLineC2Extension f)) = halfLineReflection r c2 ddf := by
    rw [heD]
    exact funext fun t => (hDD t).deriv
  have h0 := halfLineReflection_square_integral r c hr hc
    (fun t ht => (hf t ht).continuousWithinAt) hfI
  have h1 := halfLineReflection_square_integral r c1 hr hc1
    (fun t ht => (hdf t ht).continuousWithinAt) hdfI
  have h2 := halfLineReflection_square_integral r c2 hr hc2 hddf hddfI
  have hC0 : 1+(∑ j,c j^2)*(∑ j,(r j)⁻¹) ≤ 4000 := by
    norm_num [c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hC1 : 1+(∑ j,c1 j^2)*(∑ j,(r j)⁻¹) ≤ 4000 := by
    norm_num [c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hC2 : 1+(∑ j,c2 j^2)*(∑ j,(r j)⁻¹) ≤ 4000 := by
    norm_num [c2,c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  dsimp only
  rw [heDD,heD]
  refine ⟨⟨h0.1,?_⟩,⟨h1.1,?_⟩,⟨h2.1,?_⟩⟩
  · exact h0.2.trans (mul_le_mul_of_nonneg_right hC0
      (integral_nonneg (fun t => sq_nonneg (f t))))
  · exact h1.2.trans (mul_le_mul_of_nonneg_right hC1
      (integral_nonneg (fun t => sq_nonneg (df t))))
  · exact h2.2.trans (mul_le_mul_of_nonneg_right hC2
      (integral_nonneg (fun t => sq_nonneg (ddf t))))

#print axioms halfLineC2Extension_energy
end Yamabe3.Analysis.Delaunay
