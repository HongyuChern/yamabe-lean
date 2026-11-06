import Yamabe3.Analysis.Green.NativeCutoffParametrix

/-!
# Genuine compact Euclidean extensions of native smooth tests

An outer coordinate bump is first extended to the manifold. Multiplication
by the original smooth test is therefore globally smooth with compact support
inside the chart target. Its zero-extended chart pullback is the desired
genuine Euclidean test, agreeing with the original pullback on a neighborhood
of the entire inner cutoff support.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Parametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- Construct a compact smooth coordinate test from an actual native smooth
test. Every point in the inner cutoff support has a neighborhood on which
the coordinate test is exactly the native test composed with the chart. -/
theorem exists_compact_chart_test (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ e.source)
    (χ : ContDiffBump (0 : E)) (hχr : χ.rOut < r)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ ball (0 : E) r ∧
      (∀ x ∈ tsupport χ, ψ =ᶠ[𝓝 x] φ ∘ e) ∧ ψ 0 = φ (e 0) := by
  let η : ContDiffBump (0 : E) :=
    { rIn := (2 * χ.rOut + r) / 3,
      rOut := (χ.rOut + 2 * r) / 3,
      rIn_pos := by have := χ.rOut_pos; positivity,
      rIn_lt_rOut := by linarith }
  have hχη : χ.rOut < η.rIn := by dsimp [η]; linarith
  have hηr : η.rOut < r := by dsimp [η]; linarith
  have hηs : tsupport η ⊆ e.source := by
    rw [η.tsupport_eq]
    exact (closedBall_subset_closedBall hηr.le).trans hrs
  let ηM : M → ℝ := coordinateExtension e η
  have hηMs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ηM :=
    contMDiff_coordinateExtension e hei η.contDiff η.hasCompactSupport hηs
  have hηMc : HasCompactSupport ηM :=
    hasCompactSupport_coordinateExtension e η.hasCompactSupport hηs
  have hηMt : tsupport ηM ⊆ e.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_coordinateExtension_subset_image e
      η.hasCompactSupport hηs hy
    exact e.map_source (hηs hx)
  let u : M → ℝ := fun y => ηM y * φ y
  have hus : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u := hηMs.mul hφ
  have huc : HasCompactSupport u := hηMc.mul_right
  have hut : tsupport u ⊆ e.target := tsupport_mul_subset_left.trans hηMt
  let ψ : E → ℝ := chartPullback e u
  have hψeq : ψ = fun x => η x * φ (e x) := by
    funext x
    by_cases hx : x ∈ e.source
    · change chartPullback e u x = _
      rw [chartPullback_apply e u hx]
      change coordinateExtension e η (e x) * φ (e x) = _
      rw [coordinateExtension_comp_apply e η hx]
    · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h))
      simp only [ψ, chartPullback, indicator_of_notMem hx, hηx, zero_mul]
  have hψsupport : tsupport ψ ⊆ ball (0 : E) r := by
    rw [hψeq]
    exact tsupport_mul_subset_left.trans
      (by rw [η.tsupport_eq]; exact closedBall_subset_ball hηr)
  have hgerm (x : E) (hx : x ∈ tsupport χ) : ψ =ᶠ[𝓝 x] φ ∘ e := by
    have hxinner : x ∈ ball (0 : E) η.rIn :=
      (closedBall_subset_ball hχη) (χ.tsupport_eq ▸ hx)
    filter_upwards [isOpen_ball.mem_nhds hxinner] with y hy
    rw [hψeq]
    change η y * φ (e y) = φ (e y)
    rw [η.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  refine ⟨ψ, contDiff_chartPullback e he hus huc hut,
    hasCompactSupport_chartPullback e huc hut, hψsupport, hgerm, ?_⟩
  rw [hψeq]
  change η 0 * φ (e 0) = φ (e 0)
  rw [η.one_of_mem_closedBall (by simpa using η.rIn_pos.le), one_mul]

/-- The constructed coordinate extension can be consumed directly as an
actual native compact energy test for the coordinate metric. -/
theorem exists_coordinateEnergyTest (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ e.source)
    (χ : ContDiffBump (0 : E)) (hχr : χ.rOut < r)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ φ) :
    ∃ ψ : EnergyTest gE.leviCivitaData univ,
      tsupport (ψ : E → ℝ) ⊆ ball (0 : E) r ∧
      (∀ x ∈ tsupport χ, (ψ : E → ℝ) =ᶠ[𝓝 x] φ ∘ e) ∧ ψ 0 = φ (e 0) := by
  obtain ⟨ψ, hψs, hψc, hψsupport, hgerm, hzero⟩ :=
    exists_compact_chart_test e he hei hr hrs χ hχr hφ
  exact ⟨⟨ψ, hψs.contMDiff, hψc, subset_univ _⟩, hψsupport, hgerm, hzero⟩

end Yamabe3.Parametrix
