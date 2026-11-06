import Yamabe3.Analysis.NativeDomainEnergyInclusionCore
import Yamabe3.Analysis.NativeLocalCanonicalSphereTrace

/-!
# Actual domain membership for native supported multipliers

The domain space is the completion of smooth compactly supported tests in
the actual open set. Its existing inclusion into the closed native H1
space is an isometry, hence its image is closed. A smooth multiplier whose
topological support is contained in that domain produces an element of
this image, first on literal smooth tests and then on their completion.

This does not identify the global trace kernel with H1-zero on an exterior
domain. In particular no function supported inside a deleted ball is
silently removed. Exterior restriction will be obtained by an actual
convergent sequence of such supported multipliers.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory UniformSpace
open scoped Topology Manifold ContDiff

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def supportedMultiplierH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] supportedMultiplierH1NormedSpace

theorem nativeDomainEnergyInclusion_isometry (g : RiemannianMetric 3 M) (Ω : Set M) :
    Isometry (nativeDomainEnergyInclusion g Ω) := by
  let I : H1Zero g.leviCivitaData Ω →ₗᵢ[ℝ] H1Zero g.leviCivitaData univ :=
    { (nativeDomainEnergyInclusion g Ω).toLinearMap with
      norm_map' := norm_nativeDomainEnergyInclusion g Ω }
  exact I.isometry

/-- This is the actual zero-extension image of the completed domain tests. -/
theorem nativeDomainEnergyInclusion_isClosed_range
    (g : RiemannianMetric 3 M) (Ω : Set M) :
    IsClosed (Set.range (nativeDomainEnergyInclusion g Ω)) :=
  (nativeDomainEnergyInclusion_isometry g Ω).isClosedEmbedding.isClosed_range

/-- A smooth multiplier supported in the domain lands in the actual
domain completion, for the same original native H1 element. -/
theorem native_energyMulSmooth_mem_domain_range
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ Ω) (w : H1Zero g.leviCivitaData univ) :
    energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ w ∈
      Set.range (nativeDomainEnergyInclusion g Ω) := by
  induction w using Completion.induction_on with
  | hp =>
    exact (nativeDomainEnergyInclusion_isClosed_range g Ω).preimage
      (energyMulSmooth g.leviCivitaData univ
        (by simpa using isCompact_univ) χ hχ).continuous
  | ih f =>
    let p : EnergyTest g.leviCivitaData Ω :=
      ⟨f.mulSmooth χ hχ, (f.mulSmooth χ hχ).smooth,
        (f.mulSmooth χ hχ).hasCompactSupport,
        (f.mulSmooth_support_subset χ hχ).trans hs⟩
    refine ⟨(p : H1Zero g.leviCivitaData Ω), ?_⟩
    rw [nativeDomainEnergyInclusion_coe, energyMulSmooth_coe]
    congr 1

/-- The domain element is unique, not an independently selected solution. -/
theorem exists_unique_native_supported_multiplier
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ Ω) (w : H1Zero g.leviCivitaData univ) :
    ∃! v : H1Zero g.leviCivitaData Ω,
      nativeDomainEnergyInclusion g Ω v =
        energyMulSmooth g.leviCivitaData univ
          (by simpa using isCompact_univ) χ hχ w := by
  obtain ⟨v, hv⟩ := native_energyMulSmooth_mem_domain_range g Ω χ hχ hs w
  refine ⟨v, hv, ?_⟩
  intro z hz
  exact (nativeDomainEnergyInclusion_isometry g Ω).injective (hz.trans hv.symm)

/-- The same domain element retains the literal native L2 product. -/
theorem native_supported_multiplier_toL2_ae
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (w : H1Zero g.leviCivitaData univ) (v : H1Zero g.leviCivitaData Ω)
    (hv : nativeDomainEnergyInclusion g Ω v =
      energyMulSmooth g.leviCivitaData univ
        (by simpa using isCompact_univ) χ hχ w) :
    (toL2 g.leviCivitaData Ω v : M → ℝ) =ᵐ[g.volumeMeasure]
      fun x => χ x * toL2 g.leviCivitaData univ w x := by
  rw [← nativeDomainEnergyInclusion_toL2 g Ω v, hv]
  exact native_energyMulSmooth_toL2_ae g χ hχ w

/-- Any actual H1 limit of supported multipliers stays in the same
completed domain image. The caller must prove convergence. -/
theorem native_domain_range_of_tendsto
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (v : ℕ → H1Zero g.leviCivitaData univ)
    (hv : ∀ n, v n ∈ Set.range (nativeDomainEnergyInclusion g Ω))
    (w : H1Zero g.leviCivitaData univ) (hw : Tendsto v atTop (𝓝 w)) :
    w ∈ Set.range (nativeDomainEnergyInclusion g Ω) :=
  (nativeDomainEnergyInclusion_isClosed_range g Ω).mem_of_tendsto hw
    (Eventually.of_forall hv)

#print axioms nativeDomainEnergyInclusion_isClosed_range
#print axioms native_energyMulSmooth_mem_domain_range
#print axioms exists_unique_native_supported_multiplier
#print axioms native_supported_multiplier_toL2_ae
#print axioms native_domain_range_of_tendsto

end Yamabe3.Analysis
