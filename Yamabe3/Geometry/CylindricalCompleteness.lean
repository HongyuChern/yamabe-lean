import GreenMass.SingularCompleteness
import Yamabe3.Geometry.ConformalYamabe

/-!
# Native completeness from a cylindrical lower bound at a puncture

The logarithm of one plus the actual cutoff Newton singularity is a smooth
proper function on the native puncture. Its actual differential has size at
most 1/r in a Gauss chart. Thus a lower bound u^2 >= c/r is sufficient for
completeness of the genuine fourth-power conformal metric. The compact core
is handled by its actual continuous gradient quotient.

The local lower bound remains an explicit analytic input: this theorem does
not construct a nonlinear Yamabe solution or assert such an input for it.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace PoincareMT
open scoped Manifold ContDiff Topology Bundle

namespace Yamabe3.Geometry.CylindricalCompleteness

open GreenMass.PuncturedEnd GreenMass.SingularProperBarrier
open GreenMass.SingularDerivative GreenMass.SingularCompleteness Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

def logarithmicBarrier
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) : puncture (e 0) → ℝ :=
  fun q => Real.log (1 + singularBarrier e χ q)

omit [IsManifold (𝓡 3) ∞ M] in
theorem one_add_singularBarrier_pos
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (q : puncture (e 0)) :
    0 < 1 + singularBarrier e χ q := by
  have h := singular_nonneg e.toOpenPartialHomeomorph χ q.val
  change 0 ≤ singularBarrier e χ q at h
  linarith

omit [IsManifold (𝓡 3) ∞ M] in
theorem contMDiff_logarithmicBarrier
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (logarithmicBarrier e χ) :=
  contMDiff_log_of_pos (contMDiff_const.add (contMDiff_singularBarrier e χ hχ))
    (one_add_singularBarrier_pos e χ)

omit [IsManifold (𝓡 3) ∞ M] in
theorem isCompact_logarithmicBarrier_sublevel [CompactSpace M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) (R : ℝ) :
    IsCompact {q : puncture (e 0) | logarithmicBarrier e χ q ≤ R} := by
  have heq : {q : puncture (e 0) | logarithmicBarrier e χ q ≤ R} =
      {q : puncture (e 0) | singularBarrier e χ q ≤ Real.exp R - 1} := by
    ext q
    change Real.log (1 + singularBarrier e χ q) ≤ R ↔ _
    rw [Real.log_le_iff_le_exp (one_add_singularBarrier_pos e χ q)]
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact isCompact_singularBarrier_sublevel e χ hχ _

theorem abs_mvfderiv_logarithmicBarrier_le
    (g : RiemannianMetric 3 M)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    {x : E} (hx : x ∈ ball 0 χ.rIn) (hx0 : x ≠ 0)
    (hgauss : ∀ w : E, g.pullbackCoefficients e x x w = inner ℝ x w)
    (q : puncture (e 0)) (hq : q.val = e x) (v : TangentSpace (𝓡 3) q) :
    |mvfderiv (𝓡 3) (logarithmicBarrier e χ) q v| ≤
      ‖x‖⁻¹ * (restrictMetric g (puncture (e 0))).tangentNorm q v := by
  have hpos := one_add_singularBarrier_pos e χ q
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y : puncture (e 0) => 1 + singularBarrier e χ y) :=
    contMDiff_const.add (contMDiff_singularBarrier e χ hχ)
  have hchain : mvfderiv (𝓡 3) (logarithmicBarrier e χ) q v =
      (1 + singularBarrier e χ q)⁻¹ * mvfderiv (𝓡 3) (singularBarrier e χ) q v := by
    change mvfderiv (𝓡 3) (Real.log ∘ (fun y => 1 + singularBarrier e χ y)) q v = _
    have hd := Real.hasDerivAt_log hpos.ne'
    rw [mvfderiv_comp q hd.differentiableAt.mdifferentiableAt
      ((hs q).mdifferentiableAt (by simp))]
    simp only [ContinuousLinearMap.comp_apply, mvfderiv, mfderiv_eq_fderiv]
    rw [hd.hasFDerivAt.fderiv]
    change mvfderiv (𝓡 3) (fun y => 1 + singularBarrier e χ y) q v *
      (1 + singularBarrier e χ q)⁻¹ = _
    rw [mvfderiv_fun_add mdifferentiableAt_const
      (((contMDiff_singularBarrier e χ hχ) q).mdifferentiableAt (by simp))]
    simp only [mvfderiv_const, zero_add]
    exact mul_comm _ _
  have hS : singularBarrier e χ q = ‖x‖⁻¹ := by
    unfold singularBarrier
    rw [hq]
    exact singular_eq_inv_norm_near_center e.toOpenPartialHomeomorph χ hχ
      (ball_subset_closedBall hx)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hcoeff : (1 + ‖x‖⁻¹)⁻¹ * (‖x‖ ^ 2)⁻¹ ≤ ‖x‖⁻¹ := by
    have hleft : (1 + ‖x‖⁻¹)⁻¹ ≤ ‖x‖ := by
      apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 1 + ‖x‖⁻¹)).mpr
      rw [mul_add, mul_one, mul_inv_cancel₀ hn.ne']
      linarith
    calc
      (1 + ‖x‖⁻¹)⁻¹ * (‖x‖ ^ 2)⁻¹ ≤ ‖x‖ * (‖x‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hleft (inv_nonneg.mpr (sq_nonneg _))
      _ = ‖x‖⁻¹ := by field_simp
  rw [hchain, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  calc
    (1 + singularBarrier e χ q)⁻¹ * |mvfderiv (𝓡 3) (singularBarrier e χ) q v| ≤
        (1 + singularBarrier e χ q)⁻¹ * ((‖x‖ ^ 2)⁻¹ *
          (restrictMetric g (puncture (e 0))).tangentNorm q v) :=
      mul_le_mul_of_nonneg_left
        (abs_mvfderiv_singularBarrier_le g g.leviCivitaData e χ hχ hx hx0 hgauss q hq v)
        (inv_nonneg.mpr hpos.le)
    _ ≤ ‖x‖⁻¹ * (restrictMetric g (puncture (e 0))).tangentNorm q v := by
      rw [hS, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)

theorem metricComplete_of_cylindrical_lower_bound [CompactSpace M]
    (g : RiemannianMetric 3 M)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hgauss : ∀ x ∈ ball (0 : E) ρ, ∀ w : E,
      g.pullbackCoefficients e x x w = inner ℝ x w)
    (u : puncture (e 0) → ℝ) (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    (hupos : ∀ q, 0 < u q)
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hlower : ∀ (q : puncture (e 0)) (x : E), q.val = e x →
      0 < ‖x‖ → ‖x‖ < r → c * ‖x‖⁻¹ ≤ u q ^ 2) :
    MetricComplete (MetricSurgery.positiveScaling (restrictMetric g (puncture (e 0)))
      (fun q => u q ^ 4) (hu.pow 4) (fun q => pow_pos (hupos q) 4)) := by
  let δ : ℝ := min r (min ρ χ.rIn)
  have hδ : 0 < δ := lt_min hr (lt_min hρ χ.rIn_pos)
  have hδr : δ ≤ r := min_le_left _ _
  have hδρ : δ ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hδin : δ ≤ χ.rIn := (min_le_right _ _).trans (min_le_right _ _)
  have hball : ball (0 : E) δ ⊆ e.source := by
    intro x hx
    apply hχ
    rw [χ.tsupport_eq, mem_closedBall, dist_zero_right]
    exact ((by simpa using hx : ‖x‖ < δ).trans_le hδin).le.trans χ.rIn_lt_rOut.le
  let K : Set (puncture (e 0)) := (puncturedChartEnd e δ hδ hball).targetᶜ
  have hK : IsCompact K := puncturedChartEnd_complement_isCompact e δ hδ hball
  let gO := restrictMetric g (puncture (e 0))
  have hlocal : ∀ q ∉ K, ∀ v : TangentSpace (𝓡 3) q,
      |mvfderiv (𝓡 3) (logarithmicBarrier e χ) q v| ≤
        c⁻¹ * u q ^ 2 * gO.tangentNorm q v := by
    intro q hq v
    have hqt : q ∈ (puncturedChartEnd e δ hδ hball).target := by
      simpa only [K, mem_compl_iff, not_not] using hq
    rw [puncturedChartEnd_target e δ hδ hball] at hqt
    obtain ⟨x, hx, hxq⟩ := hqt
    have hx0 : x ≠ 0 := by
      intro hz
      exact q.property (by simp [← hxq, hz])
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxδ : ‖x‖ < δ := by simpa using hx
    have hlow := hlower q x hxq.symm hxn (hxδ.trans_le hδr)
    have hcoeff : ‖x‖⁻¹ ≤ c⁻¹ * u q ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hlow (inv_pos.mpr hc).le
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
    exact (abs_mvfderiv_logarithmicBarrier_le g e χ hχ
      (by simpa using hxδ.trans_le hδin) hx0
      (hgauss x (by simpa using hxδ.trans_le hδρ)) q hxq.symm v).trans
        (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _))
  obtain ⟨C, hC, hbound⟩ := exists_global_conformal_derivative_bound
    gO gO.leviCivitaData u (logarithmicBarrier e χ) hu hupos
    (contMDiff_logarithmicBarrier e χ hχ) K hK c⁻¹ hlocal
  exact metricComplete_conformal_of_constant_barrier_bound gO u (logarithmicBarrier e χ)
    hu hupos (contMDiff_logarithmicBarrier e χ hχ)
    (isCompact_logarithmicBarrier_sublevel e χ hχ) hC hbound

#print axioms contMDiff_logarithmicBarrier
#print axioms isCompact_logarithmicBarrier_sublevel
#print axioms abs_mvfderiv_logarithmicBarrier_le
#print axioms metricComplete_of_cylindrical_lower_bound

end Yamabe3.Geometry.CylindricalCompleteness
