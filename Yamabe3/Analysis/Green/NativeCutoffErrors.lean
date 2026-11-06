import Yamabe3.Analysis.Green.CutoffNewtonLimits
import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition
import PoincareLib.Geometry.Riemannian.ScalarOperators.Product
import PoincareLib.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# The native cutoff error and its singular limit

The background is an arbitrary actual smooth Riemannian metric on Euclidean
coordinate space. In the main construction it is the global metric extension
of the normalized chart. All cutoff-error coefficients below are formed from
its native Laplacian and gradient, then their support and convergence are proved.
No point-source test identity is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace Yamabe3.Parametrix

open PoincareMT
open PoincareMT.LeviCivitaData

local notation "E3" => RegularizedNewton.E

def radialQuadratic (x : E3) : ℝ := ‖x‖ ^ 2

lemma contMDiff_radialQuadratic : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ radialQuadratic :=
  (contDiff_id.norm_sq ℝ).contMDiff

def cutoffGradientCoefficient (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) (x : E3) : ℝ :=
  g.inner x (g.leviCivitaData.gradient χ x) (g.leviCivitaData.gradient radialQuadratic x)

def cutoffError (g : RiemannianMetric 3 E3) (χ : ContDiffBump (0 : E3))
    (ε : ℝ) (x : E3) : ℝ :=
  -(g.leviCivitaData.laplacian χ x) * RegularizedNewton.potential ε x +
    cutoffGradientCoefficient g χ x * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))

def singularCutoffError (g : RiemannianMetric 3 E3) (χ : ContDiffBump (0 : E3))
    (x : E3) : ℝ :=
  -(g.leviCivitaData.laplacian χ x) * ‖x‖⁻¹ +
    cutoffGradientCoefficient g χ x * (‖x‖ ^ 3)⁻¹

theorem native_gradient_potential (g : RiemannianMetric 3 E3) {ε : ℝ}
    (hε : 0 < ε) (x : E3) :
    g.leviCivitaData.gradient (RegularizedNewton.potential ε) x =
      (-(1 / 2 : ℝ) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) •
        g.leviCivitaData.gradient radialQuadratic x := by
  have hF : HasDerivAt (fun t : ℝ => (t + ε ^ 2) ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) (‖x‖ ^ 2) := by
    convert! ((hasDerivAt_id (‖x‖ ^ 2)).add_const (ε ^ 2)).rpow_const
      (p := -(1 / 2 : ℝ)) (Or.inl (RegularizedNewton.normSq_add_sq_pos hε x).ne') using 1
    norm_num
  have h := g.leviCivitaData.gradient_comp
    (contMDiff_radialQuadratic.contMDiffAt.mdifferentiableAt (by simp)) hF.differentiableAt
  change g.leviCivitaData.gradient (RegularizedNewton.potential ε) x =
    deriv (fun t : ℝ => (t + ε ^ 2) ^ (-(1 / 2 : ℝ))) (‖x‖ ^ 2) •
      g.leviCivitaData.gradient radialQuadratic x at h
  rw [hF.deriv] at h
  exact h

/-- Exact native conformal-Laplacian product formula with the cutoff error
written entirely in terms of actual metric derivatives of the chosen bump. -/
theorem native_conformalLaplacian_cutoff (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) {ε : ℝ} (hε : 0 < ε) (x : E3) :
    -g.leviCivitaData.laplacian (fun y => χ y * RegularizedNewton.potential ε y) x +
        (g.leviCivitaData.scalarCurvature x / 8) * (χ x * RegularizedNewton.potential ε x) =
      χ x * (-g.leviCivitaData.laplacian (RegularizedNewton.potential ε) x +
        (g.leviCivitaData.scalarCurvature x / 8) * RegularizedNewton.potential ε x) +
      cutoffError g χ ε x := by
  have hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ : E3 → ℝ) := χ.contDiff.contMDiff
  have hΦ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (RegularizedNewton.potential ε) :=
    ((RegularizedNewton.contDiff_potential hε).of_le le_top).contMDiff
  rw [g.leviCivitaData.laplacian_mul hχ hΦ, native_gradient_potential g hε]
  simp only [map_smul, smul_eq_mul]
  unfold cutoffError cutoffGradientCoefficient
  ring

theorem native_laplacian_bump_zero_inner (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) {x : E3} (hx : ‖x‖ < χ.rIn) :
    g.leviCivitaData.laplacian χ x = 0 := by
  have heq := χ.eventuallyEq_one_of_mem_ball (by simpa using hx)
  rw [g.leviCivitaData.laplacian_eq_of_eventuallyEq heq]
  change g.leviCivitaData.laplacian (fun _ : E3 => (1 : ℝ)) x = 0
  simp [LeviCivitaData.laplacian, LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    mvfderiv_const]

theorem cutoffGradientCoefficient_zero_inner (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) {x : E3} (hx : ‖x‖ < χ.rIn) :
    cutoffGradientCoefficient g χ x = 0 := by
  have heq := χ.eventuallyEq_one_of_mem_ball (by simpa using hx)
  have hg : g.leviCivitaData.gradient χ x = 0 := by
    unfold LeviCivitaData.gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
    change (g.inner x).inverse (mvfderiv (𝓡 3) (fun _ : E3 => (1 : ℝ)) x) = 0
    simp only [mvfderiv_const, map_zero]
  unfold cutoffGradientCoefficient
  rw [hg, map_zero, zero_apply]

theorem continuous_cutoffGradientCoefficient (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) : Continuous (cutoffGradientCoefficient g χ) :=
  g.leviCivitaData.continuous_inner_gradient χ.contDiff.contMDiff contMDiff_radialQuadratic

theorem hasCompactSupport_cutoffGradientCoefficient (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) : HasCompactSupport (cutoffGradientCoefficient g χ) :=
  g.leviCivitaData.hasCompactSupport_inner_gradient χ.hasCompactSupport radialQuadratic

theorem continuous_singularCutoffError (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) : Continuous (singularCutoffError g χ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply ContinuousAt.congr_of_eventuallyEq
      (continuousAt_const : ContinuousAt (fun _ : E3 => (0 : ℝ)) 0)
    filter_upwards [Metric.ball_mem_nhds (0 : E3) χ.rIn_pos] with y hy
    have hy' : ‖y‖ < χ.rIn := by simpa using hy
    simp only [singularCutoffError, native_laplacian_bump_zero_inner g χ hy',
      cutoffGradientCoefficient_zero_inner g χ hy', neg_zero, zero_mul, add_zero]
  · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    exact ((g.leviCivitaData.continuous_laplacian χ.contDiff.contMDiff).continuousAt.neg.mul
      (continuous_norm.continuousAt.inv₀ hnorm)).add
        ((continuous_cutoffGradientCoefficient g χ).continuousAt.mul
          ((continuous_norm.continuousAt.pow 3).inv₀ (pow_ne_zero _ hnorm)))

theorem hasCompactSupport_singularCutoffError (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) : HasCompactSupport (singularCutoffError g χ) :=
  (g.leviCivitaData.hasCompactSupport_laplacian χ.hasCompactSupport).neg.mul_right.add
    (hasCompactSupport_cutoffGradientCoefficient g χ).mul_right

/-- The cutoff part of the limiting residual belongs to the genuine L2
space for the actual coordinate metric's native volume. -/
theorem memLp_singularCutoffError (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) : MemLp (singularCutoffError g χ) 2 g.volumeMeasure :=
  (continuous_singularCutoffError g χ).memLp_of_hasCompactSupport
    (hasCompactSupport_singularCutoffError g χ)

private theorem continuous_weighted_coefficient {m c : E3 → ℝ} {s : Set E3}
    (hs : IsOpen s) (hm : ContinuousOn m s) (hc : Continuous c) (hcs : tsupport c ⊆ s) :
    Continuous (fun x => m x * c x) := by
  apply continuous_of_tsupport
  intro x hx
  exact (hm.continuousAt (hs.mem_nhds (hcs (tsupport_mul_subset_right hx)))).mul hc.continuousAt

/-- The Laplacian-of-cutoff term has the required limit without a singular
dominating function: its coefficient vanishes on the fixed inner ball. -/
theorem tendsto_integral_native_laplacian_cutoff (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) {s : Set E3} (hsOpen : IsOpen s)
    (hχ : tsupport χ ⊆ s) {m : E3 → ℝ} (hm : ContinuousOn m s) :
    Tendsto (fun ε : ℝ => ∫ x : E3,
      (m x * g.leviCivitaData.laplacian χ x) * RegularizedNewton.potential ε x)
      (𝓝 0) (𝓝 (∫ x : E3, (m x * g.leviCivitaData.laplacian χ x) * ‖x‖⁻¹)) := by
  have hc : Continuous (fun x : E3 => m x * g.leviCivitaData.laplacian χ x) :=
    continuous_weighted_coefficient hsOpen hm
      (g.leviCivitaData.continuous_laplacian χ.contDiff.contMDiff)
      ((g.leviCivitaData.tsupport_laplacian_subset χ).trans hχ)
  have hs : HasCompactSupport (fun x : E3 => m x * g.leviCivitaData.laplacian χ x) :=
    (g.leviCivitaData.hasCompactSupport_laplacian χ.hasCompactSupport).mul_left
  have hz : ∀ x : E3, ‖x‖ < χ.rIn → m x * g.leviCivitaData.laplacian χ x = 0 := by
    intro x hx
    rw [native_laplacian_bump_zero_inner g χ hx, mul_zero]
  simpa [RegularizedNewton.potential] using
    RegularizedNewton.tendsto_integral_annular_coefficient hc hs χ.rIn_pos hz 1

/-- The actual native radial-gradient pairing gives the other cutoff error
term. Its continuity, compact support, and inner vanishing are proved above. -/
theorem tendsto_integral_native_gradient_cutoff (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) {s : Set E3} (hsOpen : IsOpen s)
    (hχ : tsupport χ ⊆ s) {m : E3 → ℝ} (hm : ContinuousOn m s) :
    Tendsto (fun ε : ℝ => ∫ x : E3,
      (m x * cutoffGradientCoefficient g χ x) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))
      (𝓝 0) (𝓝 (∫ x : E3, (m x * cutoffGradientCoefficient g χ x) * (‖x‖ ^ 3)⁻¹)) := by
  have hc := continuous_weighted_coefficient hsOpen hm (continuous_cutoffGradientCoefficient g χ)
    ((g.leviCivitaData.tsupport_inner_gradient_subset_left χ radialQuadratic).trans hχ)
  have hs := (hasCompactSupport_cutoffGradientCoefficient g χ).mul_left (f := m)
  have hz : ∀ x : E3, ‖x‖ < χ.rIn → m x * cutoffGradientCoefficient g χ x = 0 := by
    intro x hx
    rw [cutoffGradientCoefficient_zero_inner g χ hx, mul_zero]
  exact RegularizedNewton.tendsto_integral_annular_coefficient hc hs χ.rIn_pos hz 3

/-- The complete cutoff-error pairing has a limit, with only local continuity
of the multiplier on an open neighborhood of the cutoff support. In particular,
the multiplier may be the actual chart density times the pulled-back test. -/
theorem tendsto_integral_native_cutoffError (g : RiemannianMetric 3 E3)
    (χ : ContDiffBump (0 : E3)) {s : Set E3} (hsOpen : IsOpen s)
    (hχ : tsupport χ ⊆ s) {m : E3 → ℝ} (hm : ContinuousOn m s) :
    Tendsto (fun ε : ℝ => ∫ x : E3, m x * cutoffError g χ ε x)
      (𝓝 0) (𝓝 (∫ x : E3, m x * singularCutoffError g χ x)) := by
  have hcL := continuous_weighted_coefficient hsOpen hm
    (g.leviCivitaData.continuous_laplacian χ.contDiff.contMDiff)
    ((g.leviCivitaData.tsupport_laplacian_subset χ).trans hχ)
  have hsL := (g.leviCivitaData.hasCompactSupport_laplacian χ.hasCompactSupport).mul_left (f := m)
  have hzL : ∀ x : E3, ‖x‖ < χ.rIn → m x * g.leviCivitaData.laplacian χ x = 0 := by
    intro x hx
    rw [native_laplacian_bump_zero_inner g χ hx, mul_zero]
  have hcB := continuous_weighted_coefficient hsOpen hm (continuous_cutoffGradientCoefficient g χ)
    ((g.leviCivitaData.tsupport_inner_gradient_subset_left χ radialQuadratic).trans hχ)
  have hsB := (hasCompactSupport_cutoffGradientCoefficient g χ).mul_left (f := m)
  have hzB : ∀ x : E3, ‖x‖ < χ.rIn → m x * cutoffGradientCoefficient g χ x = 0 := by
    intro x hx
    rw [cutoffGradientCoefficient_zero_inner g χ hx, mul_zero]
  have hiL (ε : ℝ) : Integrable (fun x : E3 =>
      (m x * g.leviCivitaData.laplacian χ x) * RegularizedNewton.potential ε x) := by
    simpa [RegularizedNewton.potential] using
      RegularizedNewton.integrable_annular_coefficient hcL hsL χ.rIn_pos hzL ε 1
  have hiB (ε : ℝ) : Integrable (fun x : E3 =>
      (m x * cutoffGradientCoefficient g χ x) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) :=
    RegularizedNewton.integrable_annular_coefficient hcB hsB χ.rIn_pos hzB ε 3
  have splitε (ε : ℝ) : (∫ x : E3, m x * cutoffError g χ ε x) =
      -(∫ x : E3, (m x * g.leviCivitaData.laplacian χ x) * RegularizedNewton.potential ε x) +
        ∫ x : E3, (m x * cutoffGradientCoefficient g χ x) *
          (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = ∫ x : E3, -((m x * g.leviCivitaData.laplacian χ x) * RegularizedNewton.potential ε x) +
          (m x * cutoffGradientCoefficient g χ x) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by unfold cutoffError; ring
      _ = _ := by
        simpa only [Pi.neg_apply, integral_neg] using integral_add (hiL ε).neg (hiB ε)
  have hiL0 : Integrable (fun x : E3 => (m x * g.leviCivitaData.laplacian χ x) * ‖x‖⁻¹) := by
    simpa only [pow_one] using
      RegularizedNewton.integrable_singular_annular_coefficient hcL hsL χ.rIn_pos hzL 1
  have hiB0 := RegularizedNewton.integrable_singular_annular_coefficient hcB hsB χ.rIn_pos hzB 3
  have split0 : (∫ x : E3, m x * singularCutoffError g χ x) =
      -(∫ x : E3, (m x * g.leviCivitaData.laplacian χ x) * ‖x‖⁻¹) +
        ∫ x : E3, (m x * cutoffGradientCoefficient g χ x) * (‖x‖ ^ 3)⁻¹ := by
    calc
      _ = ∫ x : E3, -((m x * g.leviCivitaData.laplacian χ x) * ‖x‖⁻¹) +
          (m x * cutoffGradientCoefficient g χ x) * (‖x‖ ^ 3)⁻¹ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by unfold singularCutoffError; ring
      _ = _ := by
        simpa only [Pi.neg_apply, integral_neg] using integral_add hiL0.neg hiB0
  have hsum := (tendsto_integral_native_laplacian_cutoff g χ hsOpen hχ hm).neg.add
    (tendsto_integral_native_gradient_cutoff g χ hsOpen hχ hm)
  rw [split0]
  exact hsum.congr' (Eventually.of_forall fun ε => (splitε ε).symm)

end Yamabe3.Parametrix
