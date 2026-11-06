import Yamabe3.Analysis.NativePointEnergySequence
import Yamabe3.Analysis.NativeForcedEnergySpace
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization

/-! Removal of a single point for an ACTUAL H1 field with an ACTUAL
continuous source functional. A proved native energy cutoff sequence
approximates every smooth test by tests vanishing near the point. This
does not permit a general distributional point source to be discarded. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def pointRemovalNativeH1Normed (g:RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] pointRemovalNativeH1Normed

theorem native_test_approximation_off_point
    (g:RiemannianMetric 3 M) (q:M)
    (κ:ℕ→EnergyTest g.leviCivitaData univ)
    (hκ:∀n,(κ n:M→ℝ)=ᶠ[𝓝 q](fun _=>1))
    (hκ0:Tendsto (fun n=>(κ n:H1Zero g.leviCivitaData univ)) atTop (𝓝 0))
    (φ:EnergyTest g.leviCivitaData univ) :
    ∃ψ:ℕ→EnergyTest g.leviCivitaData univ,
      (∀n,tsupport (ψ n:M→ℝ)⊆{q}ᶜ) ∧
      Tendsto (fun n=>(ψ n:H1Zero g.leviCivitaData univ)) atTop (𝓝 (φ:H1Zero g.leviCivitaData univ)) := by
  let ψ:ℕ→EnergyTest g.leviCivitaData univ:=fun n=>φ-(κ n).mulSmooth φ φ.smooth
  refine ⟨ψ,?_,?_⟩
  · intro n x hx
    change x≠q
    intro heq
    subst x
    have he:(ψ n:M→ℝ)=ᶠ[𝓝 q](fun _=>0):=by
      filter_upwards [hκ n] with x hx
      change φ x-φ x*κ n x=0
      rw [hx,mul_one,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  · obtain ⟨C,hC,hbound⟩:=exists_mulSmooth_norm_bound (D:=g.leviCivitaData) (Ω:=univ)
      (φ:M→ℝ) φ.smooth φ.hasCompactSupport
    have hkn:Tendsto (fun n=>‖κ n‖) atTop (𝓝 0):=by
      simpa only [Completion.norm_coe] using tendsto_zero_iff_norm_tendsto_zero.mp hκ0
    have hmn:Tendsto (fun n=>‖(κ n).mulSmooth φ φ.smooth‖) atTop (𝓝 0):=
      squeeze_zero (fun n=>norm_nonneg _) (fun n=>hbound (κ n)) (by
        simpa only [mul_zero] using hkn.const_mul C)
    have hm:Tendsto (fun n=>((κ n).mulSmooth φ φ.smooth:H1Zero g.leviCivitaData univ)) atTop (𝓝 0):=by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Completion.norm_coe] using hmn
    simpa only [ψ,Completion.coe_sub,sub_zero] using
      (tendsto_const_nhds (x:=(φ:H1Zero g.leviCivitaData univ))).sub hm

theorem native_point_supported_tests_determine
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {R:ℝ} (hR:0<R) (hRK:closedBall (0:E) R⊆K)
    (L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (hL:∀φ:EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆{e 0}ᶜ →
      L (φ:H1Zero g.leviCivitaData univ)=0) :
    ∀η:H1Zero g.leviCivitaData univ,L η=0 := by
  obtain ⟨κ,hκ,hκ0⟩:=exists_nativePointEnergyCutoffSequence g e he hei hK hKs hR hRK
  intro η
  induction η using Completion.induction_on with
  | hp => exact isClosed_eq L.continuous continuous_const
  | ih φ =>
    obtain ⟨ψ,hψ,hlim⟩:=native_test_approximation_off_point g (e 0) κ hκ hκ0 φ
    exact (isClosed_eq L.continuous continuous_const).mem_of_tendsto hlim
      (Eventually.of_forall (fun n=>hL (ψ n) (hψ n)))

variable [CompactSpace M] [ConnectedSpace M]

theorem native_H1_L2_equation_remove_point
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {R:ℝ} (hR:0<R) (hRK:closedBall (0:E) R⊆K)
    (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hlocal:∀φ:EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆{e 0}ᶜ →
      closedYamabeJacobianForm g B hB W (φ:H1Zero g.leviCivitaData univ)=
        inner ℝ F (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))) :
    ∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g B hB W η=inner ℝ F (toL2 g.leviCivitaData univ η) := by
  let L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ:=
    closedYamabeJacobianForm g B hB W-(innerSL ℝ F).comp (toL2 g.leviCivitaData univ)
  have hh:=native_point_supported_tests_determine g e he hei hK hKs hR hRK L
    (fun φ hs=>sub_eq_zero.mpr (hlocal φ hs))
  intro η
  exact sub_eq_zero.mp (hh η)

#print axioms native_test_approximation_off_point
#print axioms native_point_supported_tests_determine
#print axioms native_H1_L2_equation_remove_point
end Yamabe3.Analysis.SpherePolar
