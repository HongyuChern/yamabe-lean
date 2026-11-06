import Yamabe3.Geometry.FiniteEndBounds
import Yamabe3.Geometry.NativeCylindricalReference
import Yamabe3.Geometry.PuncturedConnected

/-!
# Native metric and geodesic completeness for every prescribed cylindrical end

Each one-puncture comparison metric is actually constructed. The global
comparison constants follow from the lower bounds at all deleted points
and compactness of the original background. Actual inclusion differentials
then compare intrinsic distances, and the Hausdorff limit argument excludes
every deleted point from a Cauchy limit. The all-initial-data global smooth
geodesics are obtained from this proved native metric completeness.

The nonlinear solution and its end lower bounds remain analytic inputs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Geometry.CylindricalCompleteness

open PoincareMT Yamabe3.Parametrix GreenMass.PuncturedEnd

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- Transport the actual one-puncture metric along the proved center
equality before choosing its dependent subtype and metric. -/
theorem metricComplete_sqrtNewtonFactor_at
    (g : RiemannianMetric 3 M)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hGauss : ∀ x ∈ ball (0 : E) ρ, ∀ w : E,
      g.pullbackCoefficients e x x w = inner ℝ x w)
    (p : M) (hep : e 0 = p) :
    let u : puncture p → ℝ := fun q => sqrtNewtonFactor e.toOpenPartialHomeomorph χ q.val
    ∃ (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ q, 0 < u q),
      MetricComplete (MetricSurgery.positiveScaling (restrictMetric g (puncture p))
        (fun q => u q ^ 4) (hu.pow 4) (fun q => pow_pos (hpos q) 4)) := by
  subst p
  exact metricComplete_sqrtNewtonFactor g e χ hχ ρ hρ hGauss

theorem native_complete_finite_cylindrical_ends
    (g : RiemannianMetric 3 M) (Λ : Finset M) (hΛ : Λ.Nonempty)
    (u : M → ℝ)
    (hu : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (Λ : Set M)ᶜ)
    (hupos : ∀ y ∉ Λ, 0 < u y)
    (e : M → OpenPartialHomeomorph E M) (χ : M → ContDiffBump (0 : E))
    (h0 : ∀ p ∈ Λ, (0 : E) ∈ (e p).source)
    (hep : ∀ p ∈ Λ, e p 0 = p)
    (he : ∀ p ∈ Λ, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e p) (e p).source)
    (hei : ∀ p ∈ Λ, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e p).symm (e p).target)
    (hχ : ∀ p ∈ Λ, tsupport (χ p) ⊆ (e p).source)
    (ρ : M → ℝ) (hρ : ∀ p ∈ Λ, 0 < ρ p)
    (hGauss : ∀ p ∈ Λ, ∀ x ∈ ball (0 : E) (ρ p), ∀ w : E,
      g.pullbackCoefficients (e p) x x w = inner ℝ x w)
    (c r : M → ℝ) (hc : ∀ p ∈ Λ, 0 < c p) (hr : ∀ p ∈ Λ, 0 < r p)
    (hlower : ∀ p ∈ Λ, ∀ x : E, e p x ∉ Λ → 0 < ‖x‖ → ‖x‖ < r p →
      c p * ‖x‖⁻¹ ≤ u (e p x) ^ 2) :
    let O := finitePuncture Λ
    let U : O → ℝ := fun y => u y.val
    ∃ (hU : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ U) (hpos : ∀ y, 0 < U y),
      let ghat := MetricSurgery.positiveScaling (restrictMetric g O)
        (fun y => U y ^ 4) (hU.pow 4) (fun y => pow_pos (hpos y) 4)
      MetricComplete ghat ∧ (∀ x y : O, ghat.edist x y ≠ ⊤) ∧
      ∀ (x : O) (v : E), ∃ γ : ℝ → O,
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ ∧ ghat.IsGeodesicOn γ univ ∧ γ 0 = x ∧
        HasDerivAt (fun t => extChartAt (𝓡 3) x (γ t)) v 0 := by
  classical
  let O := finitePuncture Λ
  let U : O → ℝ := fun y => u y.val
  have hU : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ U := contMDiff_restrict_of_contMDiffOn O hu
  have hpos : ∀ y : O, 0 < U y := fun y => hupos y.val y.property
  let ghat := MetricSurgery.positiveScaling (restrictMetric g O)
    (fun y => U y ^ 4) (hU.pow 4) (fun y => pow_pos (hpos y) 4)
  let V : M → M → ℝ := fun p => sqrtNewtonFactor (e p) (χ p)
  have hVs (p : M) (hp : p ∈ Λ) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun q : puncture p => V p q.val) := by
    apply contMDiff_restrict_of_contMDiffOn (puncture p)
    change ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (sqrtNewtonFactor (e p) (χ p)) ({p}ᶜ)
    simpa only [hep p hp] using contMDiffOn_sqrtNewtonFactor (e p) (hei p hp) (χ p) (hχ p hp)
  have hVp (p : M) : ∀ q : puncture p, 0 < V p q.val :=
    fun q => sqrtNewtonFactor_pos (e p) (χ p) q.val
  let gP : ∀ p ∈ Λ, RiemannianMetric 3 (puncture p) := fun p hp =>
    MetricSurgery.positiveScaling (restrictMetric g (puncture p)) (fun q => V p q.val ^ 4)
      ((hVs p hp).pow 4) (fun q => pow_pos (hVp p q) 4)
  have hPc (p : M) (hp : p ∈ Λ) : MetricComplete (gP p hp) := by
    let ed : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞ :=
      { toPartialEquiv := (e p).toPartialEquiv
        open_source := (e p).open_source
        open_target := (e p).open_target
        contMDiffOn_toFun := he p hp
        contMDiffOn_invFun := hei p hp }
    obtain ⟨hV, hVpos, hcomplete⟩ := metricComplete_sqrtNewtonFactor_at g ed (χ p) (hχ p hp)
      (ρ p) (hρ p hp) (hGauss p hp) p (hep p hp)
    exact hcomplete
  have hcomplete : MetricComplete ghat := by
    apply metricComplete_of_singlePuncture_comparisons Λ hΛ ghat gP hPc
    intro p hp
    obtain ⟨C, hC, hbound⟩ := exists_global_cylindrical_comparison Λ u hu hupos e χ
      h0 hep hei hχ c r hc hr hlower p hp
    refine ⟨C, hC, ?_⟩
    intro x y
    apply RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le _ _
      ((contMDiff_finitePunctureInclusion Λ p hp).of_le (by simp)) hC
    intro z v
    rw [tangentNorm_positiveScaling_fourth (restrictMetric g (puncture p))
        (fun q => V p q.val) (hVs p hp) (hVp p),
      tangentNorm_positiveScaling_fourth (restrictMetric g O) U hU hpos,
      tangentNorm_finitePunctureInclusion]
    have hsq : V p z.val ^ 2 ≤ C * U z ^ 2 := by
      rw [sqrtNewtonFactor_sq]
      exact hbound z.val z.property
    calc
      _ ≤ (C * U z ^ 2) * (restrictMetric g O).tangentNorm z v :=
        mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
      _ = _ := by ring
  refine ⟨hU, hpos, hcomplete, ?_, ?_⟩
  · intro x y
    exact edist_ne_top_of_finset_complement Λ O rfl ghat x y
  · intro x v
    exact exists_smooth_global_geodesic ghat hcomplete x v

#print axioms native_complete_finite_cylindrical_ends

end Yamabe3.Geometry.CylindricalCompleteness
