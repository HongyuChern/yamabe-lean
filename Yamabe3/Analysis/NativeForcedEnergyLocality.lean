import Yamabe3.Analysis.NativeWeakTestLocalGluing
import Yamabe3.Analysis.NativeForcedEnergySpace

/-! Actual local weak equations for the SAME completed field and SAME
source glue on compact test supports. The finite partition proof is used;
no global equation or conormal cancellation is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def nativeForcedLocalNormed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] nativeForcedLocalNormed

theorem nativeForcedEnergySpace_of_local
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω:Set M) (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hlocal:∀x∈Ω,∃V:Set M,IsOpen V ∧ x∈V ∧ (W,F)∈nativeForcedEnergySpace g B hB V):
    (W,F)∈nativeForcedEnergySpace g B hB Ω:=by
  let L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ:=
    closedYamabeJacobianForm g B hB W-(innerSL ℝ F).comp (toL2 g.leviCivitaData univ)
  intro φ hs
  apply sub_eq_zero.mp
  apply native_local_tests_determine_on_support g L Ω ?_ φ hs
  intro x hx
  obtain ⟨V,hV,hxV,he⟩:=hlocal x hx
  exact ⟨V,hV,hxV,fun ψ hψ=>sub_eq_zero.mpr (he ψ hψ)⟩

#print axioms nativeForcedEnergySpace_of_local
end Yamabe3.Analysis.SpherePolar
