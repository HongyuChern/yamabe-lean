import Yamabe3.Analysis.NativeForcedEnergySpace
import Yamabe3.Analysis.NativeForcedDirichletDataAssembly

/-! The actual supported smooth-test equation yields membership in the
genuine domain data space for the SAME field and SAME L2 source. Domain
tests are completed by continuity; a trace-kernel equation is not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def nativeForcedDataH1Normed (g:RiemannianMetric 3 M) (Ω:Set M):
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω):=inferInstance
attribute [local instance] nativeForcedDataH1Normed

theorem nativeForcedEnergySpace_mem_data
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω:Set M) (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (he:(W,F)∈nativeForcedEnergySpace g B hB Ω) :
    (W,F)∈NativeWeakEllipticDataSpace g Ω (nativeJacobianPotential g B)
      (nativeJacobianPotential_smooth g hB) := by
  have hpair:∀η:H1Zero g.leviCivitaData Ω,
      closedYamabeJacobianForm g B hB W (nativeDomainEnergyInclusion g Ω η)=
        nativeRestrictedL2SourceOperator g Ω F (nativeDomainEnergyInclusion g Ω η):=by
    intro η
    induction η using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih φ =>
      rw [nativeDomainEnergyInclusion_coe]
      let ψ:=testInclusion (D:=g.leviCivitaData) (subset_univ Ω) φ
      have hψ:tsupport (ψ:M→ℝ)⊆Ω:=φ.support_subset
      change closedYamabeJacobianForm g B hB W (ψ:H1Zero g.leviCivitaData univ)=_
      rw [he ψ hψ,nativeRestrictedL2SourceOperator_apply,L2.inner_def]
      calc
        _ = ∫y,(F:M→ℝ) y*ψ y ∂g.volumeMeasure:=by
          apply integral_congr_ae
          filter_upwards [ψ.memLp.coeFn_toLp] with y hy
          rw [toL2_coe]
          simp only [Real.inner_apply]
          change (F:M→ℝ) y*(ψ.memLp.toLp ψ) y=_
          rw [hy]
        _ = ∫y in Ω,(F:M→ℝ) y*ψ y ∂g.volumeMeasure:=by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro y hy
          rw [image_eq_zero_of_notMem_tsupport (fun h=>hy (hψ h)),mul_zero]
        _ = _:=by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae (s:=Ω) ψ.memLp.coeFn_toLp] with y hy
          rw [toL2_coe]
          change (F:M→ℝ) y*ψ y=(F:M→ℝ) y*(ψ.memLp.toLp ψ) y
          rw [hy]
  rw [mem_NativeWeakEllipticDataSpace_iff]
  intro η
  rw [←nativeJacobianForm_eq_elliptic g B hB,hpair,nativeRestrictedL2SourceOperator_apply,
    nativeDomainEnergyInclusion_toL2]

#print axioms nativeForcedEnergySpace_mem_data
end Yamabe3.Analysis.SpherePolar
