import Yamabe3.Analysis.NativeFiniteWindowEnergy
import Yamabe3.Analysis.NativeC2CollarEnergyBound
import Yamabe3.Analysis.NativeFiniteAllScaleField

/-! Uniform physical H2 bounds on every exterior half-end collar from
actual bounded scalar C2 coefficients. The physical exp(4s) cost is kept. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem exists_nativeFinite_halfEnd_H2_bound :
    ∃C : ℝ,0≤C ∧ ∀(m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ)
      (hq : ∀i∈m,ContDiff ℝ 2 (q i)) (A B : AngularIndex→ℝ),
      (∀i∈m,0≤A i) → (∀i∈m,0≤B i) →
      (∀i∈m,∀t≤1,‖q i t‖≤A i) →
      (∀i∈m,∀t≤1,‖deriv (deriv (q i)) t‖≤B i) →
      ∀s : ℝ,s≤0 →
      ‖nativeFiniteAllScaleJet m q hq s‖^2≤
        C*Real.exp (4*s)*(∑i∈m,((A i)^2+2*((B i)^2+angularEnergyWeight i^4*(A i)^2))) := by
  obtain ⟨C,hC,h⟩ := exists_nativeC2Collar_energy_bound
  refine ⟨C*(2*Real.exp 2),by positivity,fun m q hq A B hA hB h0 h2 s hs => ?_⟩
  let r := fun i => weightedTimeShift s (q i)
  have hr (i : AngularIndex) (hi : i∈m) := weightedTimeShift_C2 s (hq i hi)
  have h0r (i : AngularIndex) (hi : i∈m) (t : ℝ) (ht : t∈Ioo (-1:ℝ) 1) :
      ‖r i t‖≤Real.exp (2*s)*A i := by
    change ‖Real.exp (2*s)*q i (t+s)‖≤_
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (h0 i hi (t+s) (by linarith [ht.2])) (Real.exp_pos _).le
  have h2r (i : AngularIndex) (hi : i∈m) (t : ℝ) (ht : t∈Ioo (-1:ℝ) 1) :
      ‖deriv (deriv (r i)) t‖≤Real.exp (2*s)*B i := by
    rw [show deriv (deriv (r i))=weightedTimeShift s (deriv (deriv (q i))) from weightedTimeShift_second s (hq i hi)]
    simp only [weightedTimeShift,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (h2 i hi (t+s) (by linarith [ht.2])) (Real.exp_pos _).le
  have he := native_finitePhysical_window_energy m r hr (fun i => Real.exp (2*s)*A i)
    (fun i => Real.exp (2*s)*B i) (fun i hi => mul_nonneg (Real.exp_pos _).le (hA i hi))
    (fun i hi => mul_nonneg (Real.exp_pos _).le (hB i hi)) h0r h2r
  have hpow : Real.exp (2*s)^2=Real.exp (4*s) := by
    rw [←Real.exp_nat_mul];congr 1;ring
  have hsum : (∑i∈m,((Real.exp (2*s)*A i)^2+2*((Real.exp (2*s)*B i)^2+
      angularEnergyWeight i^4*(Real.exp (2*s)*A i)^2)))=
      Real.exp (4*s)*(∑i∈m,((A i)^2+2*((B i)^2+angularEnergyWeight i^4*(A i)^2))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_pow,hpow]
    ring
  rw [hsum] at he
  have hjet := h ⟨finitePhysical m r,finitePhysical_contDiffOn_offZero_C2 m r hr⟩
  change ‖nativeFiniteAllScaleJet m q hq s‖^2≤C*nativeC2WindowEnergy (finitePhysical m r) at hjet
  exact hjet.trans ((mul_le_mul_of_nonneg_left he hC).trans_eq (by ring))

#print axioms exists_nativeFinite_halfEnd_H2_bound
end Yamabe3.Analysis.SpherePolar
