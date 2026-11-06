import Yamabe3.Analysis.NativeHomogeneousEnergyRepresentative
import Yamabe3.Analysis.NativeLocalCanonicalSphereTrace
import Yamabe3.Analysis.SupportMultiplierAe

/-! An actual core cutoff of the SAME homogeneous energy field has a
smooth global representative and an actually constructed L2 operator
source. Nothing is assumed about its missing physical source identity. -/
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
private def nativeCoreSourceH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] nativeCoreSourceH1Normed

theorem nativeClosedJacobian_symm
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (W Z:H1Zero g.leviCivitaData univ):
    closedYamabeJacobianForm g B hB W Z=closedYamabeJacobianForm g B hB Z W:=by
  simp only [closedYamabeJacobianForm_apply,closedYamabeForm]
  rw [schrodingerForm_symm,potentialForm_symm]

theorem nativeSmoothTest_actual_L2_source
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (ψ:EnergyTest g.leviCivitaData univ):
    ∃F:Lp ℝ 2 g.volumeMeasure,
      (F:M→ℝ)=ᵐ[g.volumeMeasure](fun x=>-8*g.leviCivitaData.laplacian ψ x+
        (g.leviCivitaData.scalarCurvature x-30*B x^4)*ψ x) ∧
      ∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g B hB (ψ:H1Zero g.leviCivitaData univ) η=
        inner ℝ F (toL2 g.leviCivitaData univ η):=by
  let A:M→ℝ:=fun x=>-8*g.leviCivitaData.laplacian ψ x+
    (g.leviCivitaData.scalarCurvature x-30*B x^4)*ψ x
  have hm:MemLp A 2 g.volumeMeasure:=by
    have hpot:= (ψ.mulSmooth (fun x=>g.leviCivitaData.scalarCurvature x-30*B x^4)
      (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul (hB.pow 4)))).memLp
    exact (ψ.laplacian_memLp.const_mul (-8)).add hpot
  let F:=hm.toLp A
  have hF:(F:M→ℝ)=ᵐ[g.volumeMeasure]A:=hm.coeFn_toLp
  refine ⟨F,hF,fun η=>?_⟩
  rw [nativeClosedJacobian_symm,closedYamabeJacobianForm_test_eq_integral,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF] with x hx
  simp only [Real.inner_apply]
  rw [hx]
  dsimp only [A]
  ring

theorem nativeHomogeneousCore_actual_source
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω:Set M} (hΩ:IsOpen Ω) (κ:EnergyTest g.leviCivitaData univ)
    (hs:tsupport (κ:M→ℝ)⊆Ω) (W:nativeHomogeneousEnergySpace g B hB Ω):
    ∃ψ:EnergyTest g.leviCivitaData univ,
      (ψ:M→ℝ)=(fun x=>κ x*nativeHomogeneousEnergyRepresentative g B hB hΩ W x) ∧
      (ψ:H1Zero g.leviCivitaData univ)=
        energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) κ κ.smooth W.val ∧
      ∃F:Lp ℝ 2 g.volumeMeasure,
        (F:M→ℝ)=ᵐ[g.volumeMeasure](fun x=>-8*g.leviCivitaData.laplacian ψ x+
          (g.leviCivitaData.scalarCurvature x-30*B x^4)*ψ x) ∧
        ∀η:H1Zero g.leviCivitaData univ,
          closedYamabeJacobianForm g B hB
            (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) κ κ.smooth W.val) η=
              inner ℝ F (toL2 g.leviCivitaData univ η):=by
  let U:=nativeHomogeneousEnergyRepresentative g B hB hΩ W
  have hU:=nativeHomogeneousEnergyRepresentative_spec g B hB hΩ W
  have hsm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (fun x=>κ x*U x):=by
    intro x
    by_cases hx:x∈Ω
    · exact κ.smooth.contMDiffAt.mul (hU.1.contMDiffAt (hΩ.mem_nhds hx))
    · have hn:x∉tsupport (κ:M→ℝ):=fun h=>hx (hs h)
      apply contMDiffAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      change κ y*U y=0
      simp only [hy,Pi.zero_apply,zero_mul]
  let ψ:EnergyTest g.leviCivitaData univ:=
    ⟨fun x=>κ x*U x,hsm,HasCompactSupport.of_compactSpace _,subset_univ _⟩
  have hψ:(ψ:H1Zero g.leviCivitaData univ)=
      energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) κ κ.smooth W.val:=by
    apply toL2_injective
    apply Lp.ext
    rw [toL2_coe]
    have he:=supported_mul_ae_of_restrict hΩ.measurableSet (κ:M→ℝ) hs hU.2.1
    exact ψ.memLp.coeFn_toLp.trans (he.trans (native_energyMulSmooth_toL2_ae g κ κ.smooth W.val).symm)
  obtain ⟨F,hF,hweak⟩:=nativeSmoothTest_actual_L2_source g B hB ψ
  exact ⟨ψ,rfl,hψ,F,hF,fun η=>by rw [←hψ];exact hweak η⟩

#print axioms nativeClosedJacobian_symm
#print axioms nativeSmoothTest_actual_L2_source
#print axioms nativeHomogeneousCore_actual_source
end Yamabe3.Analysis.SpherePolar
