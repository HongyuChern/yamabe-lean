import GreenMass.SingularDerivative
import Yamabe3.Analysis.NativeGreenGrowth
import Yamabe3.Geometry.Completeness
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling

/-!
# Completeness of the actual continuously corrected Green metric

The native cutoff singularity supplies a smooth proper barrier on the actual
puncture. Its derivative is bounded near the pole by the true Gauss identity
and the proved inverse-radius lower bound. A continuous gradient quotient on
the compact complement supplies the remaining global bound. Rescaling the
barrier proves completeness for the actual fourth-power conformal metric.

No Green derivative asymptotics, AF estimate, distance formula, or completeness
assumption is used. The Green construction and positivity supply the displayed
actual smooth positive conformal factor and continuous correction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace PoincareMT
open scoped Manifold ContDiff Topology Bundle

namespace GreenMass.SingularCompleteness

open PuncturedEnd SingularProperBarrier SingularDerivative Yamabe3.Parametrix Yamabe3.Geometry

section CompactCore

variable {n : ℕ} {N : Type*} [TopologicalSpace N] [T3Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

/-- A local conformal derivative bound extends across an actual compact
core by bounding the true continuous gradient quotient there. -/
theorem exists_global_conformal_derivative_bound
    (g : RiemannianMetric n N) (D : LeviCivitaData g)
    (G S : N → ℝ) (hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G)
    (hGpos : ∀ q, 0 < G q) (hS : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ S)
    (K : Set N) (hK : IsCompact K) (A : ℝ)
    (hlocal : ∀ q ∉ K, ∀ v : TangentSpace (𝓡 n) q,
      |mvfderiv (𝓡 n) S q v| ≤ A * G q ^ 2 * g.tangentNorm q v) :
    ∃ C : ℝ, 0 < C ∧ ∀ q (v : TangentSpace (𝓡 n) q),
      |mvfderiv (𝓡 n) S q v| ≤ C * G q ^ 2 * g.tangentNorm q v := by
  have hratio : Continuous (fun q => g.tangentNorm q (D.gradient S q) / G q ^ 2) :=
    (D.continuous_inner_gradient hS hS).sqrt.div (hG.continuous.pow 2)
      (fun q => pow_ne_zero 2 (hGpos q).ne')
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hratio.continuousOn
  let C : ℝ := max 1 (max A B)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro q v
  by_cases hq : q ∈ K
  · have hb : g.tangentNorm q (D.gradient S q) / G q ^ 2 ≤ B :=
      (le_abs_self _).trans (hB q hq)
    have hgrad : g.tangentNorm q (D.gradient S q) ≤ C * G q ^ 2 := by
      exact ((div_le_iff₀ (sq_pos_of_pos (hGpos q))).mp hb).trans
        (mul_le_mul_of_nonneg_right hBC (sq_nonneg _))
    exact (D.abs_mvfderiv_le_gradient_norm S q v).trans
      (mul_le_mul_of_nonneg_right hgrad (Real.sqrt_nonneg _))
  · exact (hlocal q hq v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAC (sq_nonneg _)) (Real.sqrt_nonneg _))

/-- A proved finite constant is absorbed by rescaling the actual proper
barrier; the resulting conclusion is native intrinsic metric completeness. -/
theorem metricComplete_conformal_of_constant_barrier_bound
    (g : RiemannianMetric n N) (G S : N → ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G) (hGpos : ∀ q, 0 < G q)
    (hS : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ S)
    (hproper : ∀ R : ℝ, IsCompact {q : N | S q ≤ R})
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ q (v : TangentSpace (𝓡 n) q),
      |mvfderiv (𝓡 n) S q v| ≤ C * G q ^ 2 * g.tangentNorm q v) :
    MetricComplete (MetricSurgery.positiveScaling g (fun q => G q ^ 4)
      (hG.pow 4) (fun q => pow_pos (hGpos q) 4)) := by
  apply metricComplete_conformal_of_compact_sublevels_derivative_bound
    g G hG hGpos (fun q => C⁻¹ * S q)
    ((contMDiff_const.mul hS).of_le (by simp))
  · intro R
    have heq : {q : N | C⁻¹ * S q ≤ R} = {q : N | S q ≤ C * R} := by
      ext q
      simpa only [mem_ofPred_eq, div_eq_mul_inv, mul_comm] using
        (div_le_iff₀ hC : S q / C ≤ R ↔ S q ≤ R * C)
    rw [heq]
    exact hproper (C * R)
  · intro q v
    rw [mvfderiv_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹ * |mvfderiv (𝓡 n) S q v| ≤
          C⁻¹ * (C * G q ^ 2 * g.tangentNorm q v) :=
        mul_le_mul_of_nonneg_left (hbound q v) (inv_pos.mpr hC).le
      _ = G q ^ 2 * g.tangentNorm q v := by
        field_simp

end CompactCore

variable {M : Type*} [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The actual continuously corrected native cutoff Newton potential,
when smooth and positive off its pole, makes the actual restricted metric
complete. No radius construction or global lower-bound field is assumed. -/
theorem metricComplete_cutoff_minus_continuous
    (g : RiemannianMetric 3 M)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hgauss : ∀ x ∈ ball (0 : E) ρ, ∀ w : E,
      g.pullbackCoefficients e x x w = inner ℝ x w)
    (U : M → ℝ) (hU : Continuous U)
    (hG : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q : puncture (e 0) => singular e.toOpenPartialHomeomorph χ q.val - U q.val))
    (hGpos : ∀ q : puncture (e 0),
      0 < singular e.toOpenPartialHomeomorph χ q.val - U q.val) :
    MetricComplete (MetricSurgery.positiveScaling (restrictMetric g (puncture (e 0)))
      (fun q => (singular e.toOpenPartialHomeomorph χ q.val - U q.val) ^ 4)
      (hG.pow 4) (fun q => pow_pos (hGpos q) 4)) := by
  let gO := restrictMetric g (puncture (e 0))
  let G : puncture (e 0) → ℝ :=
    fun q => singular e.toOpenPartialHomeomorph χ q.val - U q.val
  obtain ⟨r, hr, hrin, hlower⟩ := singular_sub_continuous_lower_bound
    e.toOpenPartialHomeomorph χ hχ hU.continuousAt
  let δ : ℝ := min r ρ
  have hδ : 0 < δ := lt_min hr hρ
  have hδr : δ ≤ r := min_le_left _ _
  have hδρ : δ ≤ ρ := min_le_right _ _
  have hball : ball (0 : E) δ ⊆ e.source := by
    intro x hx
    apply hχ
    rw [χ.tsupport_eq, mem_closedBall, dist_zero_right]
    exact (((by simpa using hx : ‖x‖ < δ).trans_le hδr).trans_le hrin).le.trans
      χ.rIn_lt_rOut.le
  let K : Set (puncture (e 0)) := (puncturedChartEnd e δ hδ hball).targetᶜ
  have hK : IsCompact K := puncturedChartEnd_complement_isCompact e δ hδ hball
  have hlocal : ∀ q ∉ K, ∀ v : TangentSpace (𝓡 3) q,
      |mvfderiv (𝓡 3) (singularBarrier e χ) q v| ≤
        4 * G q ^ 2 * gO.tangentNorm q v := by
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
    have hxinner : x ∈ ball (0 : E) χ.rIn := by
      simpa using (hxδ.trans_le hδr).trans_le hrin
    have hxgauss : x ∈ ball (0 : E) ρ := by
      simpa using hxδ.trans_le hδρ
    have hlow : (2 * ‖x‖)⁻¹ ≤ G q := by
      change (2 * ‖x‖)⁻¹ ≤ singular e.toOpenPartialHomeomorph χ q.val - U q.val
      rw [← hxq]
      exact hlower x hxn (hxδ.trans_le hδr)
    have hsquare : ((2 * ‖x‖)⁻¹) ^ 2 ≤ G q ^ 2 :=
      (sq_le_sq₀ (inv_pos.mpr (by positivity : 0 < 2 * ‖x‖)).le (hGpos q).le).mpr hlow
    have hcoeff : (‖x‖ ^ 2)⁻¹ ≤ 4 * G q ^ 2 := by
      have hid : (‖x‖ ^ 2)⁻¹ = 4 * ((2 * ‖x‖)⁻¹) ^ 2 := by field_simp <;> norm_num
      rw [hid]
      exact mul_le_mul_of_nonneg_left hsquare (by norm_num)
    exact (abs_mvfderiv_singularBarrier_le g g.leviCivitaData e χ hχ hxinner hx0
      (hgauss x hxgauss) q hxq.symm v).trans
        (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _))
  obtain ⟨C, hC, hbound⟩ := exists_global_conformal_derivative_bound
    gO gO.leviCivitaData G (singularBarrier e χ) hG hGpos
    (contMDiff_singularBarrier e χ hχ) K hK 4 hlocal
  exact metricComplete_conformal_of_constant_barrier_bound gO G (singularBarrier e χ)
    hG hGpos (contMDiff_singularBarrier e χ hχ)
    (isCompact_singularBarrier_sublevel e χ hχ) hC hbound

#print axioms exists_global_conformal_derivative_bound
#print axioms metricComplete_conformal_of_constant_barrier_bound
#print axioms metricComplete_cutoff_minus_continuous

end GreenMass.SingularCompleteness
