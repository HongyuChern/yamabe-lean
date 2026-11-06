import Yamabe3.Analysis.NativeHomogeneousEnergySpace
import Yamabe3.Analysis.NativeDomainJacobianInverse

/-! A complete same-field/same-source energy space for genuine local
inhomogeneous equations. Unlike the homogeneous auxiliary space, nonzero
forcing is retained as a coordinate; no source-free support assumption
is silently imposed on a geometric error. Local H4 upgrades and bounded
geometric feedback are separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def forcedEnergyH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] forcedEnergyH1Normed

def nativeForcedEnergySpace (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    Submodule ℝ (H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure) where
  carrier := {z | ∀φ : EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆Ω →
    closedYamabeJacobianForm g B hB z.1 (φ:H1Zero g.leviCivitaData univ)=
      inner ℝ z.2 (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))}
  zero_mem' := by
    intro φ hs
    change closedYamabeJacobianForm g B hB 0 (φ:H1Zero g.leviCivitaData univ)=
      inner ℝ (0:Lp ℝ 2 g.volumeMeasure) _
    rw [map_zero,ContinuousLinearMap.zero_apply,inner_zero_left]
  add_mem' := by
    intro z y hz hy φ hs
    change closedYamabeJacobianForm g B hB (z.1+y.1) (φ:H1Zero g.leviCivitaData univ)=inner ℝ (z.2+y.2) _
    rw [map_add,ContinuousLinearMap.add_apply,hz φ hs,hy φ hs,inner_add_left]
  smul_mem' := by
    intro c z hz φ hs
    change closedYamabeJacobianForm g B hB (c • z.1) (φ:H1Zero g.leviCivitaData univ)=inner ℝ (c • z.2) _
    rw [map_smul,ContinuousLinearMap.smul_apply,hz φ hs,real_inner_smul_left]
    rfl

theorem nativeForcedEnergySpace_isClosed (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    IsClosed (nativeForcedEnergySpace g B hB Ω : Set (H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure)) := by
  change IsClosed {z : H1Zero g.leviCivitaData univ × Lp ℝ 2 g.volumeMeasure |
    ∀φ : EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆Ω →
      closedYamabeJacobianForm g B hB z.1 (φ:H1Zero g.leviCivitaData univ)=
        inner ℝ z.2 (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))}
  simp only [setOf_forall]
  exact isClosed_iInter fun φ => isClosed_iInter fun hs => isClosed_eq (by fun_prop) (by fun_prop)

theorem nativeForcedEnergySpace_complete (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    CompleteSpace (nativeForcedEnergySpace g B hB Ω) :=
  (nativeForcedEnergySpace_isClosed g B hB Ω).completeSpace_coe

def nativeForcedEnergyFieldCLM (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    nativeForcedEnergySpace g B hB Ω →L[ℝ] H1Zero g.leviCivitaData univ :=
  (ContinuousLinearMap.fst ℝ _ _).comp (nativeForcedEnergySpace g B hB Ω).subtypeL

def nativeForcedEnergySourceCLM (g : RiemannianMetric 3 M) (B : M→ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    nativeForcedEnergySpace g B hB Ω →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
  (ContinuousLinearMap.snd ℝ _ _).comp (nativeForcedEnergySpace g B hB Ω).subtypeL

theorem nativeForcedEnergySpace_zero_source_iff
    (g : RiemannianMetric 3 M) (B : M→ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω : Set M) (W : H1Zero g.leviCivitaData univ) :
    (W,(0:Lp ℝ 2 g.volumeMeasure))∈nativeForcedEnergySpace g B hB Ω ↔
      W∈nativeHomogeneousEnergySpace g B hB Ω := by
  change (∀φ : EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆Ω → closedYamabeJacobianForm g B hB W (φ:H1Zero g.leviCivitaData univ)=
    inner ℝ (0:Lp ℝ 2 g.volumeMeasure) (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))) ↔ _
  simp only [inner_zero_left]
  rfl

theorem nativeForcedEnergySpace_of_global_equation
    (g : RiemannianMetric 3 M) (B : M→ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω : Set M) (W : H1Zero g.leviCivitaData univ) (F : Lp ℝ 2 g.volumeMeasure)
    (h : ∀η : H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g B hB W η=
      inner ℝ F (toL2 g.leviCivitaData univ η)) :
    (W,F)∈nativeForcedEnergySpace g B hB Ω := fun φ _ => h φ

#print axioms nativeForcedEnergySpace_isClosed
#print axioms nativeForcedEnergySpace_complete
#print axioms nativeForcedEnergyFieldCLM
#print axioms nativeForcedEnergySourceCLM
#print axioms nativeForcedEnergySpace_zero_source_iff
#print axioms nativeForcedEnergySpace_of_global_equation
end Yamabe3.Analysis.SpherePolar
