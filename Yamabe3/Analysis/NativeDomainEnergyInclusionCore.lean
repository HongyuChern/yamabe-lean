import PoincareLib.Geometry.Riemannian.Connection.Construction
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Inclusion

/-!
# The same native domain inclusion, without a Yamabe inverse dependency

The six public definitions and proofs below are moved verbatim from
NativeDomainJacobianInverse. They retain the original literal smooth test,
completion map, native volume class, and energy isometry. Two additional
identities prove agreement with the fixed Poincare domain-inclusion maps.
No inverse or boundary trace is assumed or constructed by this module.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def domainInclusionCoreH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] domainInclusionCoreH1NormedSpace

/-- The actual same smooth test, with only its support declaration enlarged. -/
def nativeDomainTestInclusion (g : RiemannianMetric 3 M) (Ω : Set M) :
    EnergyTest g.leviCivitaData Ω →ₗᵢ[ℝ] EnergyTest g.leviCivitaData univ where
  toFun f := ⟨f, f.smooth, f.hasCompactSupport, subset_univ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp] theorem nativeDomainTestInclusion_apply (g : RiemannianMetric 3 M)
    (Ω : Set M) (f : EnergyTest g.leviCivitaData Ω) (x : M) :
    nativeDomainTestInclusion g Ω f x = f x := rfl

/-- The continuous extension of that isometry to the actual H1 completions. -/
def nativeDomainEnergyInclusion (g : RiemannianMetric 3 M) (Ω : Set M) :
    H1Zero g.leviCivitaData Ω →L[ℝ] H1Zero g.leviCivitaData univ :=
  Poincare.Analysis.Dirichlet.completionMap
    (Completion.toComplL.comp (nativeDomainTestInclusion g Ω).toContinuousLinearMap)

@[simp] theorem nativeDomainEnergyInclusion_coe (g : RiemannianMetric 3 M)
    (Ω : Set M) (f : EnergyTest g.leviCivitaData Ω) :
    nativeDomainEnergyInclusion g Ω (f : H1Zero g.leviCivitaData Ω) =
      (nativeDomainTestInclusion g Ω f : H1Zero g.leviCivitaData univ) :=
  Poincare.Analysis.Dirichlet.completionMap_coe _ _

@[simp] theorem norm_nativeDomainEnergyInclusion (g : RiemannianMetric 3 M)
    (Ω : Set M) (w : H1Zero g.leviCivitaData Ω) :
    ‖nativeDomainEnergyInclusion g Ω w‖ = ‖w‖ := by
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (nativeDomainEnergyInclusion g Ω).continuous.norm continuous_norm
  | ih f => simp

/-- Inclusion preserves the native L2 equivalence class, not just a formal energy norm. -/
@[simp] theorem nativeDomainEnergyInclusion_toL2 (g : RiemannianMetric 3 M)
    (Ω : Set M) (w : H1Zero g.leviCivitaData Ω) :
    toL2 g.leviCivitaData univ (nativeDomainEnergyInclusion g Ω w) =
      toL2 g.leviCivitaData Ω w := by
  induction w using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((toL2 g.leviCivitaData univ).continuous.comp (nativeDomainEnergyInclusion g Ω).continuous)
      (toL2 g.leviCivitaData Ω).continuous
  | ih f => simp only [nativeDomainEnergyInclusion_coe, toL2_coe]; rfl

/-- The literal test map is exactly the fixed original domain inclusion. -/
theorem nativeDomainTestInclusion_eq_pinned (g : RiemannianMetric 3 M) (Ω : Set M) :
    nativeDomainTestInclusion g Ω =
      testInclusion (D := g.leviCivitaData) (show Ω ⊆ univ from subset_univ Ω) := by
  rfl

/-- Moving the definitions preserves the actual continuous map, as
witnessed by equality with the pinned original completion inclusion. -/
theorem nativeDomainEnergyInclusion_eq_pinned (g : RiemannianMetric 3 M) (Ω : Set M) :
    nativeDomainEnergyInclusion g Ω =
      inclusion (D := g.leviCivitaData) (show Ω ⊆ univ from subset_univ Ω) := by
  simp only [nativeDomainEnergyInclusion,
    PoincareMT.LeviCivitaData.Dirichlet.inclusion,
    nativeDomainTestInclusion_eq_pinned]

#print axioms nativeDomainTestInclusion
#print axioms nativeDomainTestInclusion_apply
#print axioms nativeDomainEnergyInclusion
#print axioms nativeDomainEnergyInclusion_coe
#print axioms norm_nativeDomainEnergyInclusion
#print axioms nativeDomainEnergyInclusion_toL2
#print axioms nativeDomainTestInclusion_eq_pinned
#print axioms nativeDomainEnergyInclusion_eq_pinned

end Yamabe3.Analysis
