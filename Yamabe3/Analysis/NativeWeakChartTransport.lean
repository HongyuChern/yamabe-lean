import Yamabe3.Analysis.NativeWeakH01CompletionCore
import Yamabe3.Analysis.NativeCompactChartL2

/-!
# The same weak function in the actual manifold energy completion

The map below is the completion of literal coordinate extension of the
original compact smooth tests. Its bound is the proved compact-chart
metric estimate. Its L2 representative is identified through the actual
Riemannian volume map before a boundary trace is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory UniformSpace PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet

universe u
variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

private def weakChartTestNormedSpace (g : RiemannianMetric 3 M) (O : Set M) :
    NormedSpace ℝ (EnergyTest g.leviCivitaData O) := inferInstance
private def weakChartH1NormedSpace (g : RiemannianMetric 3 M) (O : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData O) := inferInstance
private def weakChartEuclideanTestNormedSpace (O : Set E) :
    NormedSpace ℝ (EnergyTest euclideanD O) := inferInstance
private def weakChartEuclideanH1NormedSpace (O : Set E) :
    NormedSpace ℝ (H1Zero euclideanD O) := inferInstance
attribute [local instance] weakChartTestNormedSpace weakChartH1NormedSpace
  weakChartEuclideanTestNormedSpace weakChartEuclideanH1NormedSpace

def nativeWeakChartTest (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E} (hOs : O ⊆ e.source) (φ : EnergyTest euclideanD O) :
    EnergyTest g.leviCivitaData (e '' O) :=
  EnergyTest.ofCoordinates e hei φ φ.smooth.contDiff φ.hasCompactSupport
    (fun x hx => ⟨hOs (φ.support_subset hx), ⟨x, φ.support_subset hx, rfl⟩⟩)

@[simp] theorem nativeWeakChartTest_apply (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E} (hOs : O ⊆ e.source) (φ : EnergyTest euclideanD O) (y : M) :
    nativeWeakChartTest g e hei hOs φ y = coordinateExtension e φ y := rfl

def nativeWeakChartTestLinear (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E} (hOs : O ⊆ e.source) :
    EnergyTest euclideanD O →ₗ[ℝ] EnergyTest g.leviCivitaData (e '' O) where
  toFun := nativeWeakChartTest g e hei hOs
  map_add' φ ψ := by
    apply Subtype.ext
    funext y
    change coordinateExtension e (fun x => φ x + ψ x) y =
      coordinateExtension e φ y + coordinateExtension e ψ y
    by_cases hy : y ∈ e.target <;> simp [coordinateExtension, hy]
  map_smul' c φ := by
    apply Subtype.ext
    funext y
    change coordinateExtension e (fun x => c * φ x) y = c * coordinateExtension e φ y
    by_cases hy : y ∈ e.target <;> simp [coordinateExtension, hy]

def nativeWeakChartBound (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) : ℝ :=
  (exists_nativeCoordinateEnergyTest_bound g e he hei hK hKs).choose

theorem nativeWeakChartBound_pos (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    0 < nativeWeakChartBound g e he hei hK hKs :=
  (exists_nativeCoordinateEnergyTest_bound g e he hei hK hKs).choose_spec.1

theorem nativeWeakChartTest_norm_le (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    (φ : EnergyTest euclideanD O) :
    ‖nativeWeakChartTest g e hei (hOK.trans hKs) φ‖ ≤
      nativeWeakChartBound g e he hei hK hKs * ‖φ‖ := by
  let ψ : EnergyTest euclideanD univ :=
    ⟨φ, φ.smooth, φ.hasCompactSupport, subset_univ _⟩
  exact (exists_nativeCoordinateEnergyTest_bound g e he hei hK hKs).choose_spec.2
    ψ (φ.support_subset.trans hOK)

private def nativeWeakChartTestToH1 (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (hOK : O ⊆ K) :
    EnergyTest euclideanD O →L[ℝ] H1Zero g.leviCivitaData (e '' O) :=
  (((Completion.toComplL : EnergyTest g.leviCivitaData (e '' O) →L[ℝ]
      H1Zero g.leviCivitaData (e '' O)).toLinearMap).comp
        (nativeWeakChartTestLinear g e hei (hOK.trans hKs))).mkContinuous
    (nativeWeakChartBound g e he hei hK hKs) (fun φ => by
      change ‖(nativeWeakChartTest g e hei (hOK.trans hKs) φ :
        H1Zero g.leviCivitaData (e '' O))‖ ≤
          nativeWeakChartBound g e he hei hK hKs * ‖φ‖
      rw [Completion.norm_coe]
      exact nativeWeakChartTest_norm_le g e he hei hK hKs hOK φ)

/-- The map is constructed from actual coordinate extensions and their
proved energy bound, rather than assumed as a Sobolev transport. -/
def nativeWeakChartH1CLM (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (hOK : O ⊆ K) :
    H1Zero euclideanD O →L[ℝ] H1Zero g.leviCivitaData (e '' O) :=
  (nativeWeakChartTestToH1 g e he hei hK hKs hOK).extend Completion.toComplL

@[simp] theorem nativeWeakChartH1CLM_coe (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    (φ : EnergyTest euclideanD O) :
    nativeWeakChartH1CLM g e he hei hK hKs hOK (φ : H1Zero euclideanD O) =
      (nativeWeakChartTest g e hei (hOK.trans hKs) φ :
        H1Zero g.leviCivitaData (e '' O)) :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (EnergyTest euclideanD O)) φ

theorem nativeWeakChartH1CLM_norm_le (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    (z : H1Zero euclideanD O) :
    ‖nativeWeakChartH1CLM g e he hei hK hKs hOK z‖ ≤
      nativeWeakChartBound g e he hei hK hKs * ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih φ =>
    rw [nativeWeakChartH1CLM_coe, Completion.norm_coe, Completion.norm_coe]
    exact nativeWeakChartTest_norm_le g e he hei hK hKs hOK φ

/-- The completed energy map and the actual volume L2 map have the same
representative. This is proved on smooth tests and then by continuity. -/
theorem toL2_nativeWeakChartH1CLM (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    (z : H1Zero euclideanD O) :
    toL2 g.leviCivitaData (e '' O) (nativeWeakChartH1CLM g e he hei hK hKs hOK z) =
      nativeCompactChartL2CLM g e he hei hK hKs (toL2 euclideanD O z) := by
  induction z using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih φ =>
    rw [nativeWeakChartH1CLM_coe, toL2_coe, toL2_coe]
    apply Lp.ext
    have hp : MemLp (testToL2 euclideanD O φ : E → ℝ) 2 volume := by
      simpa only [native_euclideanMetric_volumeMeasure] using Lp.memLp (testToL2 euclideanD O φ)
    have hφ : MemLp (φ : E → ℝ) 2 volume := by
      simpa only [native_euclideanMetric_volumeMeasure] using φ.memLp
    have hae : (testToL2 euclideanD O φ : E → ℝ) =ᵐ[volume] φ := by
      simpa only [native_euclideanMetric_volumeMeasure] using! φ.memLp.coeFn_toLp
    have hc := nativeCompactChartFunction_congr_ae g e he hei hK hKs
      (Lp.stronglyMeasurable (testToL2 euclideanD O φ)).measurable
      φ.smooth.continuous.measurable hp hφ hae
    rw [nativeCompactChartFunction_eq_of_tsupport_subset e (φ.support_subset.trans hOK)] at hc
    filter_upwards [(nativeWeakChartTest g e hei (hOK.trans hKs) φ).memLp.coeFn_toLp,
      nativeCompactChartL2Linear_ae g e he hei hK hKs (testToL2 euclideanD O φ), hc]
      with y hl hr hy
    change ((nativeWeakChartTest g e hei (hOK.trans hKs) φ).memLp.toLp _) y =
      (nativeCompactChartL2Linear g e he hei hK hKs (testToL2 euclideanD O φ) : M → ℝ) y
    exact hl.trans (hy.symm.trans hr.symm)

/-- Any two completed realizations with the same actual volume class are
equal. A later boundary trace therefore cannot depend on the chosen
compact approximants or the ambient representative. -/
theorem nativeWeakChartH01_representation_unique [PreconnectedSpace M]
    (g : RiemannianMetric 3 M) (O : Set M)
    {z w : H1Zero g.leviCivitaData O}
    (h : (toL2 g.leviCivitaData O z : M → ℝ) =ᵐ[g.volumeMeasure]
      toL2 g.leviCivitaData O w) : z = w :=
  toL2_injective (Lp.ext h)

#print axioms nativeWeakChartH1CLM_norm_le
#print axioms toL2_nativeWeakChartH1CLM
#print axioms nativeWeakChartH01_representation_unique

end Yamabe3.Analysis.SpherePolar
