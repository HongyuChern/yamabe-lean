import Yamabe3.Analysis.NativeFiniteDecayingH1

/-! The actual classical gradient and its quantitative bound, exposed
from the finite energy argument already checked in NativeFiniteDecayingH1.
This supplies actual L2 gradients for the full-source weak equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem finitePhysical_gradient_L2_of_exp_decay
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ 2 (q i)) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hvalue : ∀ i∈s, ∀t, 0≤t → ‖q i t‖≤A*Real.exp (-2*t))
    (hderiv : ∀ i∈s, ∀t, 0≤t → ‖deriv (q i) t‖≤B*Real.exp (-2*t)) :
    (∀j:Fin 3, MemLp (fun x=>fderiv ℝ (finitePhysical s q) x (EuclideanSpace.single j 1))
      2 (volume.restrict O)) ∧
    (∫ x in O, ∑j:Fin 3, (fderiv ℝ (finitePhysical s q) x (EuclideanSpace.single j 1))^2) ≤
      (∑i∈s, ((B+A/2)^2+|angularEigenvalue i| *A^2))/4 := by
  classical
  let C : ℝ := ∑i∈s, ((B+A/2)^2+|angularEigenvalue i| *A^2)
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (sq_nonneg _)))
  let energy : ℝ → ℝ := fun t=>∑i∈s,
    ((deriv (q i) t+q i t/2)^2+angularEigenvalue i*(q i t)^2)
  have hbnd (t:ℝ) (ht:0<t) : energy t≤C*Real.exp (-4*t) := by
    have he : Real.exp (-2*t)^2=Real.exp (-4*t) := by
      rw [pow_two,←Real.exp_add]
      congr 1
      ring
    rw [←he]
    change (∑i∈s, _)≤(∑i∈s, _)*_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have h0 := hvalue i hi t ht.le
    have h1 := hderiv i hi t ht.le
    have hr : ‖deriv (q i) t+q i t/2‖≤(B+A/2)*Real.exp (-2*t) := by
      calc
        _ ≤ ‖deriv (q i) t‖+‖q i t/2‖ := norm_add_le _ _
        _ = ‖deriv (q i) t‖+‖q i t‖/2 := by rw [norm_div]; norm_num
        _ ≤ (B+A/2)*Real.exp (-2*t) := by linarith
    have hs0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    have hs1 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    rw [Real.norm_eq_abs,sq_abs] at hs0 hs1
    have hm : angularEigenvalue i*(q i t)^2 ≤ |angularEigenvalue i| *(A*Real.exp (-2*t))^2 :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hs0 (abs_nonneg _))
    nlinarith only [hs1,hm]
  have hmajor : IntegrableOn (fun t:ℝ=>C*Real.exp (-4*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-4:ℝ)<0) 0).const_mul C
  have htime := native_finitePhysical_coefficient_energy_integrable_of_bound s q
    (fun i hi=>(hq i hi).contDiffOn) hmajor hbnd
  have hg := native_finitePhysical_global_gradient_energy s q (fun i hi=>(hq i hi).contDiffOn) htime
  refine ⟨hg.1,?_⟩
  rw [hg.2]
  calc
    _ ≤ ∫t in Ioi (0:ℝ), C*Real.exp (-4*t) := setIntegral_mono_on htime hmajor measurableSet_Ioi hbnd
    _ = C/4 := by
      rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-4:ℝ)<0) 0]
      norm_num <;> ring

#print axioms finitePhysical_gradient_L2_of_exp_decay
end Yamabe3.Analysis.SpherePolar
