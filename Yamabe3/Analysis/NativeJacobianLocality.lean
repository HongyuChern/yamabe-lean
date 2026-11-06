import Yamabe3.Analysis.NativeForcedEnergySpace
import Yamabe3.Analysis.NativeJacobianTestEquation

/-! Locality and exact source subtraction for the ACTUAL closed native
Jacobian. The local L2 equality is consumed through compact supported
tests; no pointwise derivative of an arbitrary L2 representative is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology Manifold
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def localJacobianH1Normed (g:RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] localJacobianH1Normed

theorem closedYamabeJacobianForm_local_ae
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω:Set M} (hΩ:MeasurableSet Ω) (W Z:H1Zero g.leviCivitaData univ)
    (he:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]
      (toL2 g.leviCivitaData univ Z:M→ℝ))
    (φ:EnergyTest g.leviCivitaData univ) (hs:tsupport (φ:M→ℝ)⊆Ω) :
    closedYamabeJacobianForm g B hB W (φ:H1Zero g.leviCivitaData univ)=
      closedYamabeJacobianForm g B hB Z (φ:H1Zero g.leviCivitaData univ) := by
  rw [closedYamabeJacobianForm_test_eq_integral,closedYamabeJacobianForm_test_eq_integral]
  apply integral_congr_ae
  have hh := (ae_restrict_iff' hΩ).mp he
  filter_upwards [hh] with x hx
  by_cases hxΩ:x∈Ω
  · rw [hx hxΩ]
  · have hxt:x∉tsupport (φ:M→ℝ) := fun ht => hxΩ (hs ht)
    rw [g.leviCivitaData.laplacian_eq_zero_of_notMem_tsupport hxt,
      image_eq_zero_of_notMem_tsupport hxt]
    simp

theorem closedYamabeJacobianForm_zero_background_local
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω:Set M} (hzero:∀x∈Ω,B x=0) (W:H1Zero g.leviCivitaData univ)
    (φ:EnergyTest g.leviCivitaData univ) (hs:tsupport (φ:M→ℝ)⊆Ω) :
    closedYamabeJacobianForm g B hB W (φ:H1Zero g.leviCivitaData univ)=
      closedYamabeJacobianForm g (fun _:M => 0) contMDiff_const W (φ:H1Zero g.leviCivitaData univ) := by
  rw [closedYamabeJacobianForm_test_eq_integral,closedYamabeJacobianForm_test_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx:x∈Ω
    · rw [hzero x hx]
    · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)),mul_zero,sub_zero]

theorem nativeForcedEnergy_same_source_subtract
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω:Set M) (W Z:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hW:(W,F)∈nativeForcedEnergySpace g B hB Ω)
    (hZ:(Z,F)∈nativeForcedEnergySpace g B hB Ω) :
    W-Z∈nativeHomogeneousEnergySpace g B hB Ω := by
  intro φ hs
  rw [map_sub,ContinuousLinearMap.sub_apply,hW φ hs,hZ φ hs,sub_self]

#print axioms closedYamabeJacobianForm_local_ae
#print axioms closedYamabeJacobianForm_zero_background_local
#print axioms nativeForcedEnergy_same_source_subtract
end Yamabe3.Analysis.SpherePolar
