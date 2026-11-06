import Yamabe3.Geometry.CylindricalCompleteness
import Yamabe3.Geometry.OpenOperators

/-!
# Complete native one-puncture cylindrical comparison metrics

The conformal factor is the actual square root of one plus the chart
cutoff Newton function. Its squared factor is exactly 1+chi/r, and the
already proved logarithmic-barrier theorem supplies native completeness.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Yamabe3.Geometry.CylindricalCompleteness

open PoincareMT Yamabe3.Parametrix GreenMass.PuncturedEnd

variable {M : Type*} [TopologicalSpace M]

def sqrtNewtonFactor (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E)) : M → ℝ :=
  fun y => Real.sqrt (1 + singular e χ y)

theorem sqrtNewtonFactor_pos (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (y : M) : 0 < sqrtNewtonFactor e χ y := by
  apply Real.sqrt_pos.mpr
  have h := singular_nonneg e χ y
  linarith

theorem sqrtNewtonFactor_sq (e : OpenPartialHomeomorph E M) (χ : ContDiffBump (0 : E))
    (y : M) : sqrtNewtonFactor e χ y ^ 2 = 1 + singular e χ y := by
  apply Real.sq_sqrt
  have h := singular_nonneg e χ y
  linarith

variable [T3Space M] [ChartedSpace E M]

theorem contMDiffOn_sqrtNewtonFactor
    (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (sqrtNewtonFactor e χ) ({e 0}ᶜ) := by
  intro y hy
  have hs := contMDiffAt_singular e hei χ hχ hy
  have hpos : 0 < 1 + singular e χ y := by
    have h := singular_nonneg e χ y
    linarith
  exact ((Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp y
    (contMDiffAt_const.add hs)).contMDiffWithinAt

variable [IsManifold (𝓡 3) ∞ M] [CompactSpace M]

theorem metricComplete_sqrtNewtonFactor
    (g : RiemannianMetric 3 M)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hGauss : ∀ x ∈ ball (0 : E) ρ, ∀ w : E,
      g.pullbackCoefficients e x x w = inner ℝ x w) :
    let u : puncture (e 0) → ℝ := fun q => sqrtNewtonFactor e.toOpenPartialHomeomorph χ q.val
    ∃ (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ q, 0 < u q),
      MetricComplete (MetricSurgery.positiveScaling (restrictMetric g (puncture (e 0)))
        (fun q => u q ^ 4) (hu.pow 4) (fun q => pow_pos (hpos q) 4)) := by
  let u : puncture (e 0) → ℝ := fun q => sqrtNewtonFactor e.toOpenPartialHomeomorph χ q.val
  have hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u :=
    contMDiff_restrict_of_contMDiffOn (puncture (e 0))
      (contMDiffOn_sqrtNewtonFactor e.toOpenPartialHomeomorph e.contMDiffOn_invFun χ hχ)
  have hpos : ∀ q, 0 < u q := fun q => sqrtNewtonFactor_pos e.toOpenPartialHomeomorph χ q.val
  refine ⟨hu, hpos, ?_⟩
  apply metricComplete_of_cylindrical_lower_bound g e χ hχ ρ hρ hGauss u hu hpos
    1 χ.rIn zero_lt_one χ.rIn_pos
  intro q x hqx hx hxr
  change 1 * ‖x‖⁻¹ ≤ sqrtNewtonFactor e.toOpenPartialHomeomorph χ q.val ^ 2
  rw [sqrtNewtonFactor_sq, hqx]
  have hsing : singular e.toOpenPartialHomeomorph χ (e x) = ‖x‖⁻¹ :=
    singular_eq_inv_norm_near_center e.toOpenPartialHomeomorph χ hχ
      (show x ∈ closedBall (0 : E) χ.rIn by simpa using hxr.le)
  rw [hsing]
  linarith

#print axioms sqrtNewtonFactor_pos
#print axioms sqrtNewtonFactor_sq
#print axioms contMDiffOn_sqrtNewtonFactor
#print axioms metricComplete_sqrtNewtonFactor

end Yamabe3.Geometry.CylindricalCompleteness
