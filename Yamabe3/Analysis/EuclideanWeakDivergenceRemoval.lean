import Yamabe3.Analysis.CompactEuclideanDivergenceRemoval
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Integration by parts for continuous fluxes with countably many
classical derivative exceptions. A genuine L1 divergence, rather than
an assumed weak equation, removes the possible point residual. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "P" => (Fin 3→ℝ)

theorem integral_test_divergence_off_countable
    {Z:E→P} (hZ:Continuous Z) {s:Set E} (hs:s.Countable)
    (hd:∀x∉s,DifferentiableAt ℝ Z x)
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ)
    (hi:Integrable (fun x:E=>φ x*(∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i))) :
    (∫x:E,φ x*(∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i))=
      -(∫x:E,∑i:Fin 3,fderiv ℝ φ x (EuclideanSpace.single i 1)*Z x i) := by
  let F:E→P:=fun x=>φ x • Z x
  have hFc:HasCompactSupport F:=hc.smul_right
  have hF:Continuous F:=hφ.continuous.smul hZ
  have hFd:∀x∉s,DifferentiableAt ℝ F x:=fun x hx=>
    (hφ.differentiable (by norm_num) x).smul (hd x hx)
  have hg:Integrable (fun x:E=>∑i:Fin 3,fderiv ℝ φ x (EuclideanSpace.single i 1)*Z x i) := by
    apply integrable_finsetSum
    intro i _
    exact (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (continuous_apply i |>.comp hZ)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right
  have hne:∀ᵐx:E ∂volume,x∉s := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hs.measure_zero (volume:Measure E)
  have he:(fun x:E=>∑i:Fin 3,fderiv ℝ F x (EuclideanSpace.single i 1) i)=ᵐ[volume]
      (fun x:E=>φ x*(∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i)+
        ∑i:Fin 3,fderiv ℝ φ x (EuclideanSpace.single i 1)*Z x i) := by
    filter_upwards [hne] with x hx
    dsimp only [F]
    rw [fderiv_fun_smul (hφ.differentiable (by norm_num) x) (hd x hx)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Finset.sum_add_distrib,Finset.mul_sum]
  have hz:=integral_compact_euclidean_divergence_off_countable hF hFc hs hFd ((hi.add hg).congr he.symm)
  rw [integral_congr_ae he,integral_add hi hg] at hz
  linarith only [hz]

#print axioms integral_test_divergence_off_countable
end Yamabe3.Analysis.UniformElliptic
