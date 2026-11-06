import Yamabe3.Analysis.Green.NativeScaledResidualJets

/-!
# Actual rescaled forcing and signed potential for the Green correction

The native residual is proved smooth away from the pole from its explicit
formula. Compactness of a genuinely joint smooth scale family bounds the
actual potential jets. Together with the proved density-residual family,
this supplies one O(r) source bound and one uniform signed-potential bound
for the centered native correction, before any scale is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set Metric Filter
open scoped ContDiff Topology Manifold

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT Yamabe3.Parametrix

/-- Smoothness of the explicit actual residual is derived on the punctured
space, including both cutoff-error terms. -/
theorem contDiffAt_nativeResidual_off_zero (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (nativeResidual g χ) x := by
  let ρ := g.pullbackVolumeDensity id
  let V : E → ℝ := fun y => g.leviCivitaData.scalarCurvature y / 8
  have hρ := native_density_smooth_positive g
  have hV : ContDiff ℝ ∞ V := g.leviCivitaData.contMDiff_scalarCurvature.contDiff.div_const 8
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hD : ContDiff ℝ ∞ (fun y : E => fderiv ℝ ρ y y) :=
    (hρ.1.fderiv_right (by simp)).clm_apply contDiff_id
  have hF : ContDiffAt ℝ ∞ (densityResidual ρ V) x := by
    exact (hD.contDiffAt.div (hρ.1.contDiffAt.mul (hn.pow 3))
      (mul_ne_zero (hρ.2 x).ne' (pow_ne_zero 3 hne))).add (hV.contDiffAt.div hn hne)
  have hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ : E → ℝ) := χ.contDiff.contMDiff
  have hLap : ContDiff ℝ ∞ (g.leviCivitaData.laplacian χ) :=
    (g.leviCivitaData.contMDiff_laplacian hχ).contDiff
  have hgrad : ContDiff ℝ ∞ (cutoffGradientCoefficient g χ) :=
    (g.leviCivitaData.contMDiff_inner_gradient hχ contMDiff_radialQuadratic).contDiff
  have herr : ContDiffAt ℝ ∞ (singularCutoffError g χ) x :=
    (hLap.contDiffAt.neg.mul (hn.inv hne)).add
      (hgrad.contDiffAt.mul ((hn.pow 3).inv (pow_ne_zero 3 hne)))
  exact (χ.contDiff.contDiffAt.mul hF).add herr

def nativePotentialDensity (g : RiemannianMetric 3 E) (x : E) : ℝ :=
  g.pullbackVolumeDensity id x * (g.leviCivitaData.scalarCurvature x / 8)

theorem contDiff_nativePotentialDensity (g : RiemannianMetric 3 E) :
    ContDiff ℝ ∞ (nativePotentialDensity g) :=
  (native_density_smooth_positive g).1.mul
    (g.leviCivitaData.contMDiff_scalarCurvature.contDiff.div_const 8)

def rescaledCorrectionPotential (g : RiemannianMetric 3 E) (r : ℝ) (x : E) : ℝ :=
  -r ^ 2 * nativePotentialDensity g (r • x)

def centeredRescaledForcing (g : RiemannianMetric 3 E) (χ : ContDiffBump (0 : E))
    (r b : ℝ) (x : E) : ℝ :=
  r ^ 2 * g.pullbackVolumeDensity id (r • x) * nativeResidual g χ (r • x) -
    (r ^ 2 * b) * nativePotentialDensity g (r • x)

theorem contDiff_rescaledCorrectionPotential (g : RiemannianMetric 3 E) (r : ℝ) :
    ContDiff ℝ ∞ (rescaledCorrectionPotential g r) :=
  contDiff_const.mul ((contDiff_nativePotentialDensity g).comp (contDiff_id.const_smul r))

theorem contDiffAt_centeredRescaledForcing (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) {r : ℝ} (hr : r ≠ 0) (b : ℝ)
    {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (centeredRescaledForcing g χ r b) x := by
  have hs : r • x ≠ 0 := smul_ne_zero hr hx
  exact (contDiffAt_const.mul
    ((native_density_smooth_positive g).1.contDiffAt.comp x
      (contDiffAt_id.const_smul r)) |>.mul
    ((contDiffAt_nativeResidual_off_zero g χ hs).comp x (contDiffAt_id.const_smul r))).sub
      (contDiffAt_const.mul ((contDiff_nativePotentialDensity g).contDiffAt.comp x
        (contDiffAt_id.const_smul r)))

private theorem norm_iteratedFDeriv_const_mul
    {w : E → ℝ} {z : E} (hw : ContDiffAt ℝ ∞ w z) (n : ℕ) (c : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x => c * w x) z‖ =
      |c| * ‖iteratedFDeriv ℝ n w z‖ := by
  change ‖iteratedFDeriv ℝ n (c • w) z‖ = _
  rw [iteratedFDeriv_const_smul_apply (hw.of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]

/-- The actual centered equation has one O(r) source bound and one common
signed-potential bound through any prescribed finite order. No scalewise
elliptic or coefficient constants occur in the premises. -/
theorem exists_uniform_native_centered_forcing_jets
    (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (k : ℕ) (b : ℝ) :
    ∃ R C Q : ℝ, 0 < R ∧ 0 ≤ C ∧ 0 ≤ Q ∧ ∀ n ≤ k,
      ∀ r : ℝ, 0 < r → r < R → ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (rescaledCorrectionPotential g r) z‖ ≤ Q ∧
      ‖iteratedFDeriv ℝ n (centeredRescaledForcing g χ r b) z‖ ≤ C * r := by
  have hW := contDiff_nativePotentialDensity g
  have hjoint : ∀ q : ℝ × E, q.2 ≠ 0 →
      ContDiffAt ℝ ∞ (fun p : ℝ × E => nativePotentialDensity g (p.1 • p.2)) q := by
    intro q _
    exact hW.contDiffAt.comp q (contDiffAt_fst.smul contDiffAt_snd)
  obtain ⟨A, hA, hAb⟩ := exists_uniform_spatial_jet_bounds hjoint k
  obtain ⟨R, C, hR, hC, hb⟩ := exists_uniform_native_scaledResidual_jet_bounds g hzero χ k
  refine ⟨min 1 R, C + A * |b|, A, lt_min (by norm_num) hR,
    add_nonneg hC (mul_nonneg hA (abs_nonneg _)), hA, ?_⟩
  intro n hn r hr hrR z hzlo hzup
  have hr1 : r ≤ 1 := (hrR.trans_le (min_le_left _ _)).le
  have hrR' : r < R := hrR.trans_le (min_le_right _ _)
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hr21 : r ^ 2 ≤ 1 := hr2.trans hr1
  have hz : z ≠ 0 := by intro hz; norm_num [hz] at hzlo
  let w : E → ℝ := fun x => nativePotentialDensity g (r • x)
  have hw : ContDiff ℝ ∞ w := hW.comp (contDiff_id.const_smul r)
  have hwB : ‖iteratedFDeriv ℝ n w z‖ ≤ A := hAb n hn r ⟨hr.le, hr1⟩ z hzlo hzup
  have hq : ‖iteratedFDeriv ℝ n (rescaledCorrectionPotential g r) z‖ ≤ A := by
    change ‖iteratedFDeriv ℝ n (fun x => -r ^ 2 * w x) z‖ ≤ A
    rw [norm_iteratedFDeriv_const_mul hw.contDiffAt]
    rw [abs_neg, abs_of_nonneg (sq_nonneg r)]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr21).trans hwB
  refine ⟨hq, ?_⟩
  let f : E → ℝ := fun x => r ^ 2 * g.pullbackVolumeDensity id (r • x) *
    nativeResidual g χ (r • x)
  have hf : ContDiffAt ℝ ∞ f z := by
    exact (contDiffAt_const.mul ((native_density_smooth_positive g).1.contDiffAt.comp z
      (contDiffAt_id.const_smul r))).mul
      ((contDiffAt_nativeResidual_off_zero g χ (smul_ne_zero hr.ne' hz)).comp z
        (contDiffAt_id.const_smul r))
  have hs : ContDiffAt ℝ ∞ (fun x => (r ^ 2 * b) * w x) z :=
    contDiffAt_const.mul hw.contDiffAt
  change ‖iteratedFDeriv ℝ n (fun x => f x - (r ^ 2 * b) * w x) z‖ ≤ _
  rw [fun_iteratedFDeriv_sub_apply
    (hf.of_le (by exact_mod_cast le_top)) (hs.of_le (by exact_mod_cast le_top))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f z‖ + ‖iteratedFDeriv ℝ n (fun x => (r ^ 2 * b) * w x) z‖ :=
      norm_sub_le _ _
    _ ≤ C * r + |r ^ 2 * b| * A := by
      rw [norm_iteratedFDeriv_const_mul hw.contDiffAt]
      exact add_le_add (hb n hn r hr hrR' z hzlo hzup).2
        (mul_le_mul_of_nonneg_left hwB (abs_nonneg _))
    _ ≤ C * r + r * |b| * A := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr2 (abs_nonneg b)) hA)
    _ = _ := by ring

#print axioms contDiffAt_nativeResidual_off_zero
#print axioms contDiff_nativePotentialDensity
#print axioms contDiff_rescaledCorrectionPotential
#print axioms contDiffAt_centeredRescaledForcing
#print axioms exists_uniform_native_centered_forcing_jets

end Yamabe3.Analysis.GreenParametrix
