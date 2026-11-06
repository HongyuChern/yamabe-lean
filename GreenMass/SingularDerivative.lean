import GreenMass.SingularProperBarrier
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Radial
import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition
import Yamabe3.Geometry.OpenRestriction

/-!
# The true derivative of the native Newton barrier near its pole

The actual Gauss pairing proves that the radial coordinate has unit gradient.
The scalar inverse chain rule and the actual cutoff germ then give the exact
inverse-square norm of the gradient of the native barrier. Restriction uses
the actual inclusion differential and the actual restricted metric.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace PoincareMT
open scoped Manifold ContDiff Topology Bundle

namespace GreenMass.SingularDerivative

open PuncturedEnd SingularProperBarrier Yamabe3.Parametrix Yamabe3.Geometry

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

/-- The Gauss pairing yields the exact unit gradient norm of the actual
coordinate radius. -/
theorem tangentNorm_gradient_radius
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) (hx0 : x ≠ 0)
    (hgauss : ∀ w : E, g.pullbackCoefficients e x x w = inner ℝ x w) :
    g.tangentNorm (e x) (D.gradient (fun y => ‖e.symm y‖) (e x)) = 1 := by
  have hrad := D.gradient_radial_coordinate e
    he hei hx hx0 hgauss
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  rw [hrad]
  change Real.sqrt (g.inner (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x (‖x‖⁻¹ • x))
    (mfderiv (𝓡 3) (𝓡 3) e x (‖x‖⁻¹ • x))) = 1
  have hpair : g.inner (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x (‖x‖⁻¹ • x))
      (mfderiv (𝓡 3) (𝓡 3) e x (‖x‖⁻¹ • x)) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    change ‖x‖⁻¹ * (‖x‖⁻¹ * g.pullbackCoefficients e x x x) = 1
    rw [hgauss x, real_inner_self_eq_norm_sq]
    field_simp
  rw [hpair, Real.sqrt_one]

/-- The cutoff equals one on the inner ball, so the native barrier has
exactly the inverse-square gradient norm there. -/
theorem tangentNorm_gradient_singular
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {x : E} (hx : x ∈ ball 0 χ.rIn) (hx0 : x ≠ 0)
    (hgauss : ∀ w : E, g.pullbackCoefficients e x x w = inner ℝ x w) :
    g.tangentNorm (e x) (D.gradient (singular e χ) (e x)) =
      (‖x‖ ^ 2)⁻¹ := by
  have hxs : x ∈ e.source := by
    apply hχ
    rw [χ.tsupport_eq]
    exact (closedBall_subset_closedBall χ.rIn_lt_rOut.le) (ball_subset_closedBall hx)
  have hex := e.map_source hxs
  have hinv := hei.contMDiffAt (e.open_target.mem_nhds hex)
  have hr : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => ‖e.symm y‖) (e x) := by
    have hn := (contDiffAt_norm ℝ
      (show e.symm (e x) ≠ 0 by simpa only [e.left_inv hxs] using hx0)
      (n := ∞)).contMDiffAt
    exact hn.comp (e x) hinv
  have heq : singular e χ =ᶠ[𝓝 (e x)]
      (fun y => ‖e.symm y‖⁻¹) := by
    have hball : ball (0 : E) χ.rIn ∈ 𝓝 (e.symm (e x)) := by
      rw [e.left_inv hxs]
      exact isOpen_ball.mem_nhds hx
    filter_upwards [e.open_target.mem_nhds hex,
      hinv.continuousAt.preimage_mem_nhds hball] with y hyt hyinner
    rw [singular_apply e χ hyt,
      χ.one_of_mem_closedBall (ball_subset_closedBall hyinner), one_mul]
  have hgerm : D.gradient (singular e χ) (e x) =
      D.gradient (fun y => ‖e.symm y‖⁻¹) (e x) := by
    unfold LeviCivitaData.gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  have hcomp : D.gradient (fun y => ‖e.symm y‖⁻¹) (e x) =
      -(‖x‖ ^ 2)⁻¹ • D.gradient (fun y => ‖e.symm y‖) (e x) := by
    have hF : DifferentiableAt ℝ (fun z : ℝ => z⁻¹) ‖e.symm (e x)‖ :=
      differentiableAt_inv (by rw [e.left_inv hxs]; exact norm_ne_zero_iff.mpr hx0)
    simpa only [Function.comp_def, deriv_inv, e.left_inv hxs] using
      D.gradient_comp (hr.mdifferentiableAt (by simp)) hF
  have hunit := tangentNorm_gradient_radius g D e he hei hxs hx0 hgauss
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change ‖D.gradient (fun y => ‖e.symm y‖) (e x)‖ = 1 at hunit
  change ‖D.gradient (singular e χ) (e x)‖ = (‖x‖ ^ 2)⁻¹
  rw [hgerm, hcomp, norm_smul, hunit, mul_one, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖x‖))]

/-- The true ambient directional derivative has the exact radial bound. -/
theorem abs_mvfderiv_singular_le
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {x : E} (hx : x ∈ ball 0 χ.rIn) (hx0 : x ≠ 0)
    (hgauss : ∀ w : E, g.pullbackCoefficients e x x w = inner ℝ x w)
    (v : TangentSpace (𝓡 3) (e x)) :
    |mvfderiv (𝓡 3) (singular e χ) (e x) v| ≤
      (‖x‖ ^ 2)⁻¹ * g.tangentNorm (e x) v := by
  have h := D.abs_mvfderiv_le_gradient_norm (singular e χ) (e x) v
  rwa [tangentNorm_gradient_singular g D e he hei χ hχ hx hx0 hgauss] at h

/-- Restriction transports the derivative estimate through the true
inclusion differential, whose norm is exactly the restricted metric norm. -/
theorem abs_mvfderiv_singularBarrier_le
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {x : E} (hx : x ∈ ball 0 χ.rIn) (hx0 : x ≠ 0)
    (hgauss : ∀ w : E, g.pullbackCoefficients e x x w = inner ℝ x w)
    (q : puncture (e 0)) (hq : q.val = e x) (v : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (singularBarrier e χ) q v| ≤
      (‖x‖ ^ 2)⁻¹ * (restrictMetric g (puncture (e 0))).tangentNorm q v := by
  have hs := (contMDiffAt_singular e.toOpenPartialHomeomorph e.contMDiffOn_invFun χ hχ
    (show q.val ≠ e 0 from q.property)).mdifferentiableAt (by simp)
  have hi := (contMDiff_subtype_val (I := 𝓡 3) (U := puncture (e 0)) (n := ∞) q).mdifferentiableAt
    (by simp)
  change |mvfderiv (𝓡 3)
    ((singular e.toOpenPartialHomeomorph χ) ∘ (Subtype.val : puncture (e 0) → M)) q v| ≤ _
  rw [mvfderiv_comp q hs hi, ContinuousLinearMap.comp_apply]
  have hb : ∀ w : TangentSpace (𝓡 3) q.val,
      |mvfderiv (𝓡 3) (singular e.toOpenPartialHomeomorph χ) q.val w| ≤
        (‖x‖ ^ 2)⁻¹ * g.tangentNorm q.val w := by
    rw [hq]
    exact abs_mvfderiv_singular_le g D e.toOpenPartialHomeomorph
      e.contMDiffOn_toFun e.contMDiffOn_invFun χ hχ hx hx0 hgauss
  exact hb (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : puncture (e 0) → M) q v)

#print axioms tangentNorm_gradient_radius
#print axioms tangentNorm_gradient_singular
#print axioms abs_mvfderiv_singular_le
#print axioms abs_mvfderiv_singularBarrier_le

end GreenMass.SingularDerivative
