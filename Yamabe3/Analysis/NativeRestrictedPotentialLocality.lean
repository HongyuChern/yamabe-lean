import Yamabe3.Analysis.NativeRestrictedPotentialEnergy

/-!
# Actual native L2 locality of the restricted potential form

The form consumes the native restricted L2 value of the same test. This
is the value component needed when a global H1 test is replaced by its
actual exterior H1-zero restriction. No gradient locality or boundary
trace restriction of an ambient almost-everywhere identity is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory UniformSpace
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def potentialLocalityNormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] potentialLocalityNormedSpace

theorem nativeRestrictedPotentialForm_eq_of_toL2_ae
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (u v w : H1Zero g.leviCivitaData univ)
    (hvalue : (toL2 g.leviCivitaData univ v : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      (toL2 g.leviCivitaData univ w : M → ℝ)) :
    nativeRestrictedPotentialForm g Ω V hV u v = nativeRestrictedPotentialForm g Ω V hV u w := by
  have heq : LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω (toL2 g.leviCivitaData univ v) =
      LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω (toL2 g.leviCivitaData univ w) := by
    apply Lp.ext
    exact (LpToLpRestrictCLM_coeFn ℝ Ω (toL2 g.leviCivitaData univ v)).trans
      (hvalue.trans (LpToLpRestrictCLM_coeFn ℝ Ω (toL2 g.leviCivitaData univ w)).symm)
  change inner ℝ _ (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω
    (toL2 g.leviCivitaData univ v)) = inner ℝ _ (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω
      (toL2 g.leviCivitaData univ w))
  rw [heq]

theorem nativeRestrictedPotentialForm_eq_of_exterior_value
    (g : RiemannianMetric 3 M) (Ω : Set M) (hΩ : MeasurableSet Ω)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (u v w : H1Zero g.leviCivitaData univ)
    (hvalue : (toL2 g.leviCivitaData univ w : M → ℝ) =ᵐ[g.volumeMeasure]
      Ω.indicator (toL2 g.leviCivitaData univ v : M → ℝ)) :
    nativeRestrictedPotentialForm g Ω V hV u v = nativeRestrictedPotentialForm g Ω V hV u w := by
  apply nativeRestrictedPotentialForm_eq_of_toL2_ae g Ω V hV u v w
  filter_upwards [ae_restrict_of_ae hvalue, self_mem_ae_restrict hΩ] with x hx hmem
  rw [indicator_of_mem hmem] at hx
  exact hx.symm

#print axioms nativeRestrictedPotentialForm_eq_of_toL2_ae
#print axioms nativeRestrictedPotentialForm_eq_of_exterior_value

end Yamabe3.Analysis
