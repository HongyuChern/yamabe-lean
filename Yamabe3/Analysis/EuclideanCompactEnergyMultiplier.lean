import Yamabe3.Analysis.NativeWeakChartCompletion
import Yamabe3.Analysis.L2BoundedScalarMultiplier
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization

/-! Actual compact smooth multiplication on the original whole-space
H1 completion. Equality with multiplication of its L2 class is proved
on dense tests and extended by continuity. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
local notation "μe" => (RiemannianMetric.euclideanMetric 3).volumeMeasure
variable (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)

include hχ hc in
private theorem compactMultiplier_bound : ∃C:ℝ,0 ≤ C ∧ ∀x:E,‖χ x‖ ≤ C := by
  obtain ⟨C,hC⟩:=hχ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  exact ⟨max C 0,le_max_right _ _,fun x=>(hC ⟨x,rfl⟩).trans (le_max_left _ _)⟩

def euclideanCompactL2MulCLM : Lp ℝ 2 μe →L[ℝ] Lp ℝ 2 μe :=
  l2ScalarMulCLM χ hχ.continuous.aestronglyMeasurable (compactMultiplier_bound χ hχ hc).choose
    (compactMultiplier_bound χ hχ hc).choose_spec.1
    (Eventually.of_forall (compactMultiplier_bound χ hχ hc).choose_spec.2)

theorem euclideanCompactL2MulCLM_ae (z:Lp ℝ 2 μe) :
    (euclideanCompactL2MulCLM χ hχ hc z:E→ℝ)=ᵐ[μe]fun x=>χ x*z x :=
  l2ScalarMul_ae χ hχ.continuous.aestronglyMeasurable (compactMultiplier_bound χ hχ hc).choose
    (compactMultiplier_bound χ hχ hc).choose_spec.1
    (Eventually.of_forall (compactMultiplier_bound χ hχ hc).choose_spec.2) z

def euclideanCompactEnergyMulCLM : H1Zero Deuc univ →L[ℝ] H1Zero Deuc univ :=
  (Completion.toComplL.comp (mulSmoothCLM Deuc univ χ hχ.contMDiff hc)).extend Completion.toComplL

theorem euclideanCompactEnergyMulCLM_coe (φ:EnergyTest Deuc univ) :
    euclideanCompactEnergyMulCLM χ hχ hc (φ:H1Zero Deuc univ)=
      (φ.mulSmooth χ hχ.contMDiff:H1Zero Deuc univ) :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (EnergyTest Deuc univ)) φ

theorem euclideanCompactEnergyMulCLM_toL2 (z:H1Zero Deuc univ) :
    toL2 Deuc univ (euclideanCompactEnergyMulCLM χ hχ hc z)=
      euclideanCompactL2MulCLM χ hχ hc (toL2 Deuc univ z) := by
  induction z using Completion.induction_on with
  | hp=>exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih φ=>
    rw [euclideanCompactEnergyMulCLM_coe,toL2_coe]
    have hi:(toL2 Deuc univ (φ:H1Zero Deuc univ):E→ℝ)=ᵐ[μe](φ:E→ℝ) := by
      rw [toL2_coe]
      exact φ.memLp.coeFn_toLp
    apply Lp.ext
    filter_upwards [(φ.mulSmooth χ hχ.contMDiff).memLp.coeFn_toLp,
      euclideanCompactL2MulCLM_ae χ hχ hc (toL2 Deuc univ (φ:H1Zero Deuc univ)),hi] with x hl hr hi
    exact hl.trans (by simpa only [EnergyTest.mulSmooth_apply,hi] using hr.symm)

theorem euclideanCompactEnergyMulCLM_ae (z:H1Zero Deuc univ) :
    (toL2 Deuc univ (euclideanCompactEnergyMulCLM χ hχ hc z):E→ℝ)=ᵐ[volume]
      fun x=>χ x*toL2 Deuc univ z x := by
  rw [euclideanCompactEnergyMulCLM_toL2]
  simpa only [native_euclideanMetric_volumeMeasure] using
    euclideanCompactL2MulCLM_ae χ hχ hc (toL2 Deuc univ z)

#print axioms euclideanCompactEnergyMulCLM_toL2
#print axioms euclideanCompactEnergyMulCLM_ae
end Yamabe3.Analysis.SpherePolar
