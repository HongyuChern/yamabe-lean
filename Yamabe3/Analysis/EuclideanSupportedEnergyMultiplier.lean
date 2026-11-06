import Yamabe3.Analysis.EuclideanCompactEnergyMultiplier
import Yamabe3.Analysis.EuclideanH1L2ClosedGraphLift
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Inclusion

/-! A genuine supported multiplier lands in the actual domain
completion, rather than merely having a vanishing L2 representative
outside it. The inclusion is an isometry and the lifted element is
unique. No trace-kernel characterization is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable (O:Set E) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆O)

include hs in
theorem euclideanCompactEnergyMul_mem_domain_range (z:H1Zero Deuc univ) :
    euclideanCompactEnergyMulCLM χ hχ hc z∈Set.range (inclusion (D:=Deuc) (subset_univ O)) := by
  induction z using Completion.induction_on with
  | hp=>
    exact ((inclusionIsometry (D:=Deuc) (subset_univ O)).isometry.isClosedEmbedding.isClosed_range).preimage
      (euclideanCompactEnergyMulCLM χ hχ hc).continuous
  | ih φ=>
    let p:EnergyTest Deuc O:=⟨φ.mulSmooth χ hχ.contMDiff,(φ.mulSmooth χ hχ.contMDiff).smooth,
      (φ.mulSmooth χ hχ.contMDiff).hasCompactSupport,(φ.mulSmooth_support_subset χ hχ.contMDiff).trans hs⟩
    refine ⟨(p:H1Zero Deuc O),?_⟩
    rw [inclusion_coe,euclideanCompactEnergyMulCLM_coe]
    congr 1

include hs in
theorem euclideanSupportedEnergyMul_exists (z:H1Zero Deuc univ) :
    ∃v:H1Zero Deuc O,toL2 Deuc O v=toL2 Deuc univ (euclideanCompactEnergyMulCLM χ hχ hc z) := by
  obtain ⟨v,hv⟩:=euclideanCompactEnergyMul_mem_domain_range O χ hχ hc hs z
  refine ⟨v,?_⟩
  rw [←hv,toL2_inclusion]

def euclideanSupportedEnergyMulCLM : H1Zero Deuc univ →L[ℝ] H1Zero Deuc O :=
  euclideanH1L2LiftCLM O ((toL2 Deuc univ).comp (euclideanCompactEnergyMulCLM χ hχ hc))
    (euclideanSupportedEnergyMul_exists O χ hχ hc hs)

theorem euclideanSupportedEnergyMulCLM_toL2 (z:H1Zero Deuc univ) :
    toL2 Deuc O (euclideanSupportedEnergyMulCLM O χ hχ hc hs z)=
      toL2 Deuc univ (euclideanCompactEnergyMulCLM χ hχ hc z) :=
  euclideanH1L2LiftCLM_toL2 _ _ _ _

theorem euclideanSupportedEnergyMulCLM_inclusion (z:H1Zero Deuc univ) :
    inclusion (D:=Deuc) (subset_univ O) (euclideanSupportedEnergyMulCLM O χ hχ hc hs z)=
      euclideanCompactEnergyMulCLM χ hχ hc z := by
  apply toL2_injective
  rw [toL2_inclusion,euclideanSupportedEnergyMulCLM_toL2]

theorem euclideanSupportedEnergyMulCLM_norm_le (z:H1Zero Deuc univ) :
    ‖euclideanSupportedEnergyMulCLM O χ hχ hc hs z‖ ≤ ‖euclideanCompactEnergyMulCLM χ hχ hc‖*‖z‖ := by
  rw [←norm_inclusion (subset_univ O) (euclideanSupportedEnergyMulCLM O χ hχ hc hs z),
    euclideanSupportedEnergyMulCLM_inclusion]
  exact (euclideanCompactEnergyMulCLM χ hχ hc).le_opNorm z

theorem euclideanSupportedEnergyMulCLM_ae (z:H1Zero Deuc univ) :
    (toL2 Deuc O (euclideanSupportedEnergyMulCLM O χ hχ hc hs z):E→ℝ)=ᵐ[volume]
      fun x=>χ x*toL2 Deuc univ z x := by
  rw [euclideanSupportedEnergyMulCLM_toL2]
  exact euclideanCompactEnergyMulCLM_ae χ hχ hc z

#print axioms euclideanCompactEnergyMul_mem_domain_range
#print axioms euclideanSupportedEnergyMulCLM_inclusion
#print axioms euclideanSupportedEnergyMulCLM_norm_le
#print axioms euclideanSupportedEnergyMulCLM_ae
end Yamabe3.Analysis.SpherePolar
