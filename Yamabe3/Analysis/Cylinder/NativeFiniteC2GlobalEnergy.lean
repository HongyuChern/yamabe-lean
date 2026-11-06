import Yamabe3.Analysis.Cylinder.NativeFiniteC2GradientEnergy
import Yamabe3.Analysis.Cylinder.NativeHalfEndPolarEnergy
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndFiniteWeakEquation

/-!
# Global original Euclidean gradient energy of finite C2 spectral fields

The actual finite-gradient identity is combined with the genuine polar
integrability transfer.  The result concerns the original coordinate
partials of the original finite physical function on the whole punctured
unit ball.  The optional majorant is a real positive-time coefficient
energy bound; no physical gradient membership is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem native_finitePhysical_global_gradient_energy
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0))
    (htime : IntegrableOn (fun t => ∑ i ∈ s,
      ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2)) (Ioi 0)) :
    (∀ j : Fin 3, MemLp (fun x => fderiv ℝ (finitePhysical s q) x
      (EuclideanSpace.single j 1)) 2
        (volume.restrict (Metric.ball (0 : E) 1 \ {(0 : E)}))) ∧
      (∫ x in Metric.ball (0 : E) 1 \ {(0 : E)},
        ∑ j : Fin 3, (fderiv ℝ (finitePhysical s q) x (EuclideanSpace.single j 1)) ^ 2) =
        ∫ t in Ioi (0 : ℝ), ∑ i ∈ s,
          ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2) := by
  have hu : ContDiffOn ℝ 1 (finitePhysical s q)
      (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
    rw [halfEnd_puncturedUnitBall_eq]
    exact (contDiffOn_finitePhysical_of_c2_positive s q hq).of_le (by norm_num)
  apply native_halfEnd_gradient_memLp_of_angular_energy hu htime
  intro t ht
  rw [integral_const_mul]
  exact native_finitePhysical_gradient_log_slice s q hq ht

/-- A proved coefficient-energy majorant produces the integrability
needed by the original Euclidean gradient theorem. -/
theorem native_finitePhysical_coefficient_energy_integrable_of_bound
    (s : Finset AngularIndex) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiffOn ℝ 2 (q i) (Ioi 0))
    {B : ℝ → ℝ} (hB : IntegrableOn B (Ioi 0))
    (hbound : ∀ t : ℝ, 0 < t → (∑ i ∈ s,
      ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2)) ≤ B t) :
    IntegrableOn (fun t => ∑ i ∈ s,
      ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2)) (Ioi 0) := by
  classical
  have hcont : ContinuousOn (fun t => ∑ i ∈ s,
      ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2)) (Ioi 0) := by
    apply continuousOn_finsetSum
    intro i hi
    exact (((hq i hi).continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).add
      ((hq i hi).continuousOn.div_const 2)).pow 2 |>.add
        (((hq i hi).continuousOn.pow 2).const_mul (angularEigenvalue i))
  have hnonneg (t : ℝ) : 0 ≤ ∑ i ∈ s,
      ((deriv (q i) t + q i t / 2) ^ 2 + angularEigenvalue i * q i t ^ 2) := by
    apply Finset.sum_nonneg
    intro i hi
    have hEig : 0 ≤ angularEigenvalue i := by
      rcases angularEigenvalue_zero_two_or_ge_six i with he | he | he
      · rw [he]
      · rw [he]; norm_num
      · linarith
    exact add_nonneg (sq_nonneg _) (mul_nonneg hEig (sq_nonneg _))
  apply hB.mono' (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (hnonneg t)]
  exact hbound t ht

#print axioms native_finitePhysical_global_gradient_energy
#print axioms native_finitePhysical_coefficient_energy_integrable_of_bound

end Yamabe3.Analysis.SpherePolar
