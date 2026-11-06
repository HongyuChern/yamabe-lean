import Yamabe3.Analysis.EuclideanCompletedDilation

/-! An arbitrary positive dilation on the original H1 completion. The
explicit bound sqrt(a^3+a) pays both the L2 and gradient terms. Small
scales retain the sharper previously proved sqrt(a) interface. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
local notation "μe" => (RiemannianMetric.euclideanMetric 3).volumeMeasure

theorem euclideanDilatedTest_arbitrary_norm_le {a:ℝ} (ha:0 < a) (O:Set E) (φ:EnergyTest Deuc O) :
    ‖euclideanDilatedTest ha O φ‖ ≤ Real.sqrt (a^3+a)*‖φ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity),euclideanDilatedTest_norm_sq,nativeEuclidean_test_norm_sq]
  have h0:0 ≤ ∫x:E,φ x^2 := integral_nonneg (fun x=>sq_nonneg _)
  have h1:0 ≤ ∑i:Fin 3,∫x:E,(fderiv ℝ (φ:E→ℝ) x (EuclideanSpace.single i 1))^2 :=
    Finset.sum_nonneg (fun i _=>integral_nonneg (fun x=>sq_nonneg _))
  nlinarith [mul_nonneg ha.le h0,mul_nonneg (pow_nonneg ha.le 3) h1]

theorem euclideanL2Dilation_arbitrary_norm_le {a:ℝ} (ha:0 < a) (f:Lp ℝ 2 μe) :
    ‖euclideanL2DilationLinear ha f‖ ≤ Real.sqrt (a^3+a)*‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [euclideanL2Dilation_norm_sq,mul_pow,Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg ha.le (sq_nonneg ‖f‖)]

def euclideanArbitraryL2DilationCLM {a:ℝ} (ha:0 < a) : Lp ℝ 2 μe →L[ℝ] Lp ℝ 2 μe :=
  (euclideanL2DilationLinear ha).mkContinuous (Real.sqrt (a^3+a)) (euclideanL2Dilation_arbitrary_norm_le ha)

theorem euclideanArbitraryL2DilationCLM_ae {a:ℝ} (ha:0 < a) (f:Lp ℝ 2 μe) :
    (euclideanArbitraryL2DilationCLM ha f:E→ℝ)=ᵐ[μe](fun x=>f (a⁻¹ • x)) :=
  (memLp_nativeEuclidean_dilation ha f).coeFn_toLp

def euclideanArbitraryDilationTestToH1 {a:ℝ} (ha:0 < a) (O:Set E) :
    EnergyTest Deuc O →L[ℝ] H1Zero Deuc (euclideanDilatedDomain a O) :=
  (((Completion.toComplL:EnergyTest Deuc (euclideanDilatedDomain a O) →L[ℝ]
    H1Zero Deuc (euclideanDilatedDomain a O)).toLinearMap).comp (euclideanDilatedTestLinear ha O)).mkContinuous
    (Real.sqrt (a^3+a)) (fun φ=>by
      change ‖(euclideanDilatedTest ha O φ:H1Zero Deuc (euclideanDilatedDomain a O))‖ ≤ _
      rw [Completion.norm_coe]
      exact euclideanDilatedTest_arbitrary_norm_le ha O φ)

def euclideanArbitraryH1DilationCLM {a:ℝ} (ha:0 < a) (O:Set E) :
    H1Zero Deuc O →L[ℝ] H1Zero Deuc (euclideanDilatedDomain a O) :=
  (euclideanArbitraryDilationTestToH1 ha O).extend Completion.toComplL

theorem euclideanArbitraryH1DilationCLM_coe {a:ℝ} (ha:0 < a) (O:Set E) (φ:EnergyTest Deuc O) :
    euclideanArbitraryH1DilationCLM ha O (φ:H1Zero Deuc O)=
      (euclideanDilatedTest ha O φ:H1Zero Deuc (euclideanDilatedDomain a O)) :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (EnergyTest Deuc O)) φ

theorem euclideanArbitraryH1DilationCLM_norm_le {a:ℝ} (ha:0 < a) (O:Set E) (z:H1Zero Deuc O) :
    ‖euclideanArbitraryH1DilationCLM ha O z‖ ≤ Real.sqrt (a^3+a)*‖z‖ := by
  induction z using Completion.induction_on with
  | hp=>exact isClosed_le (by fun_prop) (by fun_prop)
  | ih φ=>
    rw [euclideanArbitraryH1DilationCLM_coe,Completion.norm_coe,Completion.norm_coe]
    exact euclideanDilatedTest_arbitrary_norm_le ha O φ

theorem euclideanArbitraryH1DilationCLM_toL2 {a:ℝ} (ha:0 < a) (O:Set E) (z:H1Zero Deuc O) :
    toL2 Deuc (euclideanDilatedDomain a O) (euclideanArbitraryH1DilationCLM ha O z)=
      euclideanArbitraryL2DilationCLM ha (toL2 Deuc O z) := by
  induction z using Completion.induction_on with
  | hp=>exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih φ=>
    rw [euclideanArbitraryH1DilationCLM_coe,toL2_coe]
    have hin:(toL2 Deuc O (φ:H1Zero Deuc O):E→ℝ)=ᵐ[μe](φ:E→ℝ) := by
      rw [toL2_coe]
      exact φ.memLp.coeFn_toLp
    apply Lp.ext
    filter_upwards [(euclideanDilatedTest ha O φ).memLp.coeFn_toLp,
      euclideanArbitraryL2DilationCLM_ae ha (toL2 Deuc O (φ:H1Zero Deuc O)),
      ae_nativeEuclidean_dilation ha hin] with x hl hr hi
    exact hl.trans (hi.symm.trans hr.symm)

theorem euclideanArbitraryH1DilationCLM_ae {a:ℝ} (ha:0 < a) (O:Set E) (z:H1Zero Deuc O) :
    (toL2 Deuc (euclideanDilatedDomain a O) (euclideanArbitraryH1DilationCLM ha O z):E→ℝ)=ᵐ[μe]
      fun x=>toL2 Deuc O z (a⁻¹ • x) := by
  rw [euclideanArbitraryH1DilationCLM_toL2]
  exact euclideanArbitraryL2DilationCLM_ae ha _

#print axioms euclideanDilatedTest_arbitrary_norm_le
#print axioms euclideanArbitraryH1DilationCLM_norm_le
#print axioms euclideanArbitraryH1DilationCLM_toL2
#print axioms euclideanArbitraryH1DilationCLM_ae
end Yamabe3.Analysis.SpherePolar
