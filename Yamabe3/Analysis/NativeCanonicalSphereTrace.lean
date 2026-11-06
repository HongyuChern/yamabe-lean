import Yamabe3.Analysis.NativeH1SphereTraceCore

/-!
# The actual value trace of the same native energy element

An almost-everywhere smooth representative is first identified with the
same element of the native energy completion, using the proved injectivity
of its actual L2 map. Its H1 trace is consequently the literal restriction
of that representative on every admissible chart sphere. A volume-AE
identity alone is never restricted to a measure-zero sphere.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet SpherePolar

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def canonicalSphereTraceH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] canonicalSphereTraceH1NormedSpace

/-- The actual L2 representative determines the entire native energy
element, including its gradient and all continuous trace operators. -/
theorem native_energy_eq_smooth_test_of_ae
    (g : RiemannianMetric 3 M) (w : H1Zero g.leviCivitaData univ)
    (W : M → ℝ) (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W)
    (hae : W =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ w : M → ℝ)) :
    w = (UniformSpace.Completion.toComplL : EnergyTest g.leviCivitaData univ →L[ℝ]
      H1Zero g.leviCivitaData univ)
        ⟨W, hW, HasCompactSupport.of_compactSpace W, subset_univ _⟩ := by
  let φ : EnergyTest g.leviCivitaData univ :=
    ⟨W, hW, HasCompactSupport.of_compactSpace W, subset_univ _⟩
  change w = (φ : H1Zero g.leviCivitaData univ)
  apply toL2_injective
  rw [toL2_coe]
  apply Lp.ext
  exact hae.symm.trans φ.memLp.coeFn_toLp.symm

/-- The genuine H1 trace is the actual sphere restriction of this smooth
representative. This follows from energy equality, not from restriction
of an ambient almost-everywhere equality. -/
theorem nativeSphereTraceCLM_of_smooth_representative
    (g : RiemannianMetric 3 M) (w : H1Zero g.leviCivitaData univ)
    (W : M → ℝ) (hW : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ W)
    (hae : W =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ w : M → ℝ))
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source) :
    (nativeSphereTraceCLM g e he hei ha hab hr hKs w : S → ℝ) =ᵐ[angularVolume]
      nativeSphereRestriction e r W := by
  let φ : EnergyTest g.leviCivitaData univ :=
    ⟨W, hW, HasCompactSupport.of_compactSpace W, subset_univ _⟩
  have hwφ : w = (φ : H1Zero g.leviCivitaData univ) :=
    native_energy_eq_smooth_test_of_ae g w W hW hae
  have htrace := nativeSphereTraceCLM_coe g e he hei ha hab hr hKs φ
  have hvalue := nativeSphereTestTraceLinear_ae g e r
    (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) φ
  change (nativeSphereTraceCLM g e he hei ha hab hr hKs w : S → ℝ) =ᵐ[angularVolume]
    nativeSphereRestriction e r φ
  simpa only [hwφ, htrace] using hvalue


#print axioms native_energy_eq_smooth_test_of_ae
#print axioms nativeSphereTraceCLM_of_smooth_representative

end Yamabe3.Analysis
