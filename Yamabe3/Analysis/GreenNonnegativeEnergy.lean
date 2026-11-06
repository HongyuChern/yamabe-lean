import Yamabe3.Analysis.GreenCorrection
import Yamabe3.Analysis.Green.SmoothPositiveApprox
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation

/-!
# Native smooth truncation and the positive Yamabe energy gap

Every approximating test is an actual smooth function on the retained closed
manifold. The gradient chain rule and the real Yamabe L2 gap force a smooth
function with vanishing positive-part pairings to be nonpositive. The
potential may change sign. No negative-part lattice on completed H1 is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis.GreenPositivity

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The explicit scaled smooth positive-part function is a genuine energy
test on the closed manifold. -/
def positiveApproxTest (g : RiemannianMetric 3 M)
    (S : EnergyTest g.leviCivitaData univ) (δ : ℝ) :
    EnergyTest g.leviCivitaData univ :=
  ⟨fun x => smoothPositiveApprox δ (S x),
    (contDiff_smoothPositiveApprox δ).contMDiff.comp S.smooth,
    HasCompactSupport.of_compactSpace _, subset_univ _⟩

omit [ConnectedSpace M] in
/-- The scalar derivative bound is transported through the actual metric
gradient and integrated against the native volume. -/
theorem positiveApproxTest_energy_le (g : RiemannianMetric 3 M)
    (S : EnergyTest g.leviCivitaData univ) {B δ : ℝ}
    (hB : 0 ≤ B) (hVB : ∀ x, -B ≤ g.leviCivitaData.scalarCurvature x / 8)
    (hδ : 0 < δ) :
    closedConformalLaplacianForm g
        (positiveApproxTest g S δ : H1Zero g.leviCivitaData univ)
        (positiveApproxTest g S δ : H1Zero g.leviCivitaData univ) ≤
      closedConformalLaplacianForm g (S : H1Zero g.leviCivitaData univ)
        (positiveApproxTest g S δ : H1Zero g.leviCivitaData univ) +
      B * δ * ∫ x, positiveApproxTest g S δ x ∂g.volumeMeasure := by
  let D := g.leviCivitaData
  let T := positiveApproxTest g S δ
  have hgrad (x : M) : D.gradient T x =
      deriv (smoothPositiveApprox δ) (S x) • D.gradient S x := by
    exact D.gradient_comp ((S.smooth x).mdifferentiableAt (by simp))
      ((contDiff_smoothPositiveApprox δ).differentiable (by simp) (S x))
  have hcomp (x : M) :
      g.inner x (D.gradient T x) (D.gradient T x) +
          (D.scalarCurvature x / 8) * T x * T x ≤
        g.inner x (D.gradient S x) (D.gradient T x) +
          (D.scalarCurvature x / 8) * S x * T x + B * δ * T x := by
    have hA : 0 ≤ g.inner x (D.gradient S x) (D.gradient S x) := by
      by_cases hz : D.gradient S x = 0
      · simp [hz]
      · exact (g.pos x _ hz).le
    have hg : g.inner x (D.gradient T x) (D.gradient T x) ≤
        g.inner x (D.gradient S x) (D.gradient T x) := by
      rw [hgrad]
      simp only [map_smul, smul_apply, smul_eq_mul]
      simpa only [pow_two, mul_assoc] using
        mul_le_mul_of_nonneg_right (deriv_smoothPositiveApprox_sq_le hδ (S x)) hA
    have hgap := smoothPositiveApprox_potential_gap hδ (S x)
    change 0 ≤ S x * T x - (T x) ^ 2 ∧
      S x * T x - (T x) ^ 2 ≤ δ * T x at hgap
    have hv := hVB x
    have hprod := mul_nonneg (show 0 ≤ D.scalarCurvature x / 8 + B by linarith) hgap.1
    have hbound := mul_le_mul_of_nonneg_left hgap.2 hB
    nlinarith
  have hTT : Integrable (fun x =>
      g.inner x (D.gradient T x) (D.gradient T x) +
        (D.scalarCurvature x / 8) * T x * T x) g.volumeMeasure :=
    ((D.continuous_inner_gradient T.smooth T.smooth).add
      (((D.continuous_scalarCurvature.div_const 8).mul T.smooth.continuous).mul
        T.smooth.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hST : Integrable (fun x =>
      g.inner x (D.gradient S x) (D.gradient T x) +
        (D.scalarCurvature x / 8) * S x * T x) g.volumeMeasure :=
    ((D.continuous_inner_gradient S.smooth T.smooth).add
      (((D.continuous_scalarCurvature.div_const 8).mul S.smooth.continuous).mul
        T.smooth.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hT : Integrable (T : M → ℝ) g.volumeMeasure :=
    T.smooth.continuous.integrable_of_hasCompactSupport T.hasCompactSupport
  rw [closedConformalLaplacianForm_coe, closedConformalLaplacianForm_coe]
  calc
    _ ≤ ∫ x, (g.inner x (D.gradient S x) (D.gradient T x) +
        (D.scalarCurvature x / 8) * S x * T x) + B * δ * T x ∂g.volumeMeasure :=
      integral_mono hTT (hST.add (hT.const_mul (B * δ))) hcomp
    _ = _ := by
      erw [integral_add hST (hT.const_mul (B * δ)), integral_const_mul]

/-- Under the genuine positive Yamabe hypothesis, vanishing native
pairings with every actual smooth positive-part approximation force a smooth
function to be nonpositive. The proof passes to the L2 integral by dominated
convergence and uses positive native volume to recover pointwise sign. -/
theorem nonpos_of_positiveApprox_pairing_zero (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (S : EnergyTest g.leviCivitaData univ)
    (hpair : ∀ δ : ℝ, 0 < δ →
      closedConformalLaplacianForm g (S : H1Zero g.leviCivitaData univ)
        (positiveApproxTest g S δ : H1Zero g.leviCivitaData univ) = 0) :
    ∀ x : M, S x ≤ 0 := by
  let D := g.leviCivitaData
  let T := positiveApproxTest g S
  let κ : ℝ := (1 / 8) *
    (Target.yamabeConstant g / (g.volumeMeasure univ).toReal ^ (2 / 3 : ℝ))
  have hκ : 0 < κ := mul_pos (by norm_num)
    (div_pos hY (Real.rpow_pos_of_pos (volume_pos_of_yamabe_pos g hY) _))
  obtain ⟨B, hB, hVB⟩ := exists_nonneg_potential_lower_bound
    (fun x => D.scalarCurvature x / 8) (D.continuous_scalarCurvature.div_const 8)
  let K : ℝ := ∫ x, max (S x) 0 ∂g.volumeMeasure
  have hKint : Integrable (fun x => max (S x) 0) g.volumeMeasure :=
    (S.smooth.continuous.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmaxcont : Continuous (fun x => (max (S x) 0) ^ 2) :=
    (S.smooth.continuous.max continuous_const).pow 2
  have hmaxint : Integrable (fun x => (max (S x) 0) ^ 2) g.volumeMeasure :=
    hmaxcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      κ * (∫ x, (T δ x) ^ 2 ∂g.volumeMeasure) ≤ B * δ * K := by
    have hnorm : ‖testToL2 D univ (T δ)‖ ^ 2 =
        ∫ x, (T δ x) ^ 2 ∂g.volumeMeasure := by
      rw [← real_inner_self_eq_norm_sq, testToL2_inner]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by change T δ x * T δ x = (T δ x) ^ 2; ring
    have hgap := mul_le_mul_of_nonneg_left
      (closedYamabeForm_test_L2_lower g hY (T δ)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hP : κ * (∫ x, (T δ x) ^ 2 ∂g.volumeMeasure) ≤
        closedConformalLaplacianForm g (T δ : H1Zero D univ) (T δ : H1Zero D univ) := by
      rw [closedConformalLaplacianForm_apply]
      dsimp only [κ]
      rw [← hnorm]
      nlinarith
    have hupper := positiveApproxTest_energy_le g S hB hVB hδ
    rw [hpair δ hδ, zero_add] at hupper
    have hTint : Integrable (T δ : M → ℝ) g.volumeMeasure :=
      (T δ).smooth.continuous.integrable_of_hasCompactSupport (T δ).hasCompactSupport
    exact hP.trans (hupper.trans (mul_le_mul_of_nonneg_left
      (integral_mono hTint hKint (fun x => smoothPositiveApprox_le_posPart hδ (S x)))
      (mul_nonneg hB hδ.le)))
  have hlim : Tendsto (fun δ : ℝ => ∫ x, (T δ x) ^ 2 ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (∫ x, (max (S x) 0) ^ 2 ∂g.volumeMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => (max (S x) 0) ^ 2)
    · exact Eventually.of_forall fun δ => ((T δ).smooth.continuous.pow 2).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h₀ := smoothPositiveApprox_nonneg hδ (S x)
        have h₁ := smoothPositiveApprox_le_posPart hδ (S x)
        change (smoothPositiveApprox δ (S x)) ^ 2 ≤ (max (S x) 0) ^ 2
        nlinarith [le_max_right (S x) 0]
    · exact hmaxint
    · exact Eventually.of_forall fun x => (tendsto_smoothPositiveApprox (S x)).pow 2
  have hzero : κ * (∫ x, (max (S x) 0) ^ 2 ∂g.volumeMeasure) ≤ 0 := by
    apply le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hlim)
      (show Tendsto (fun δ : ℝ => B * δ * K) (𝓝[>] 0) (𝓝 0) from by
        have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [mul_zero, zero_mul] using (hid.const_mul B).mul_const K)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hbound δ hδ
  intro x
  by_contra hx
  have hpos : 0 < S x := lt_of_not_ge hx
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have hIntPos : 0 < ∫ x, (max (S x) 0) ^ 2 ∂g.volumeMeasure :=
    integral_pos_of_integrable_nonneg_nonzero hmaxcont hmaxint
      (fun x => sq_nonneg _) (x := x) (by
        rw [max_eq_left hpos.le]
        exact pow_ne_zero 2 hpos.ne')
  exact (not_lt_of_ge hzero) (mul_pos hκ hIntPos)

#print axioms positiveApproxTest_energy_le
#print axioms nonpos_of_positiveApprox_pairing_zero

end Yamabe3.Analysis.GreenPositivity
