import Yamabe3.Analysis.NativeForcedDirichletDataAssembly
import Yamabe3.Analysis.NativeWeakPhysicalH1Gluing
import Yamabe3.Analysis.NativeForcedThreeRegionGluing

/-! Actual source-subtracted native flux identity for ONE completed
field and ONE source. A global weak equation is used only in the final
consumer below; the actual source producer is assembled separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeWeakEnergySourceData_add_compl
    (g:RiemannianMetric 3 M) (Ω:Set M) (hΩ:MeasurableSet Ω)
    (V:M→ℝ) (hV:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V)
    (Z:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (η:H1Zero g.leviCivitaData univ):
    nativeWeakEnergySourceDataCLM g Ω V hV (Z,F) η+
      nativeWeakEnergySourceDataCLM g Ωᶜ V hV (Z,F) η=
      schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ) 8 V hV Z η-
        ∫y,F y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure:=by
  have hg:=nativeRestrictedGradientEnergy_add_compl g Ω hΩ Z η
  have hpI:Integrable (fun y=>V y*toL2 g.leviCivitaData univ Z y*toL2 g.leviCivitaData univ η y) g.volumeMeasure:=by
    simpa only [IntegrableOn,Measure.restrict_univ] using nativeRestrictedPotentialForm_integrable g univ V hV Z η
  have hp:=integral_add_compl hΩ hpI
  rw [←nativeRestrictedPotentialForm_integral g Ω V hV Z η,
    ←nativeRestrictedPotentialForm_integral g Ωᶜ V hV Z η,
    ←nativeGlobalPotentialForm_integral g V hV Z η] at hp
  have hsI:Integrable (fun y=>F y*toL2 g.leviCivitaData univ η y) g.volumeMeasure:=
    (Lp.memLp F).integrable_mul (Lp.memLp (toL2 g.leviCivitaData univ η))
  have hs:=integral_add_compl hΩ hsI
  rw [nativeWeakEnergySourceDataCLM_apply,nativeWeakEnergySourceDataCLM_apply,
    nativeRestrictedEllipticForm_apply,nativeRestrictedEllipticForm_apply,
    nativeRestrictedL2SourceOperator_apply,nativeRestrictedL2SourceOperator_apply,schrodingerForm_apply]
  dsimp only [Prod.fst,Prod.snd]
  linarith only [hg,hp,hs]

theorem nativeForcedGlobal_actual_conormal_balance
    (g:RiemannianMetric 3 M) (Ω:Set M) (hΩ:MeasurableSet Ω)
    (Z:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (h:(Z,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const univ):
    ∀η:H1Zero g.leviCivitaData univ,
      nativeWeakEnergySourceDataCLM g Ω (nativeJacobianPotential g (fun _:M=>0))
        (nativeJacobianPotential_smooth g contMDiff_const) (Z,F) η+
      nativeWeakEnergySourceDataCLM g Ωᶜ (nativeJacobianPotential g (fun _:M=>0))
        (nativeJacobianPotential_smooth g contMDiff_const) (Z,F) η=0:=by
  intro η
  rw [nativeWeakEnergySourceData_add_compl g Ω hΩ]
  rw [schrodingerForm_apply]
  rw [←nativeJacobianForm_eq_elliptic g (fun _:M=>0) contMDiff_const]
  rw [nativeForcedEnergySpace_global_all_tests g (fun _:M=>0) contMDiff_const Z F h η,L2.inner_def]
  apply sub_eq_zero.mpr
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>by simp only [Real.inner_apply])

#print axioms nativeWeakEnergySourceData_add_compl
#print axioms nativeForcedGlobal_actual_conormal_balance
end Yamabe3.Analysis.SpherePolar
