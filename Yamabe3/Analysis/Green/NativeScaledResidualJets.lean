import Yamabe3.Analysis.Green.NativeScaledResidual
import Yamabe3.Analysis.Green.UniformResidualJets

/-!
# Uniform jets of the actual rescaled native parametrix forcing

Both the native source F and the coordinate divergence source rho*F are
identified with r times an actual jointly smooth family. Every spatial
derivative through a prescribed finite order therefore has one O(r) bound,
with the same radius and constant for all scales on the fixed annulus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Set Metric Filter
open scoped ContDiff Topology Manifold

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT Yamabe3.Parametrix

theorem exists_uniform_native_scaledResidual_jet_bounds
    (g : RiemannianMetric 3 E)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (k : ℕ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ n ≤ k, ∀ r : ℝ, 0 < r → r < R → ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun x => r ^ 2 * nativeResidual g χ (r • x)) z‖ ≤ C * r ∧
      ‖iteratedFDeriv ℝ n (fun x => r ^ 2 * g.pullbackVolumeDensity id (r • x) *
        nativeResidual g χ (r • x)) z‖ ≤ C * r := by
  let ρ : E → ℝ := g.pullbackVolumeDensity id
  let V : E → ℝ := fun y => g.leviCivitaData.scalarCurvature y / 8
  have hρ := native_density_smooth_positive g
  have hV : ContDiff ℝ ∞ V := g.leviCivitaData.contMDiff_scalarCurvature.contDiff.div_const 8
  have hF := contDiffAt_scaledDensityResidual hρ.1 hρ.2 hV
  have hW := contDiffAt_weightedScaledDensityResidual hρ.1 hρ.2 hV
  obtain ⟨C1, hC1, hb1⟩ := exists_uniform_spatial_jet_bounds hF k
  obtain ⟨C2, hC2, hb2⟩ := exists_uniform_spatial_jet_bounds hW k
  let R : ℝ := min 1 (χ.rIn / 4)
  let C : ℝ := max C1 C2
  refine ⟨R, C, lt_min (by norm_num) (div_pos χ.rIn_pos (by norm_num)),
    hC1.trans (le_max_left _ _), ?_⟩
  intro n hn r hr hrR z hzlo hzup
  have hr1 : r ≤ 1 := (hrR.trans_le (min_le_left _ _)).le
  have hrχ : r < χ.rIn / 4 := hrR.trans_le (min_le_right _ _)
  have hz : z ≠ 0 := by intro heq; norm_num [heq] at hzlo
  have hnorm : ‖r • z‖ < χ.rIn := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  let f : E → ℝ := fun x => scaledDensityResidual ρ V (r, x)
  let w : E → ℝ := fun x => weightedScaledDensityResidual ρ V (r, x)
  have heq : (fun x => r ^ 2 * nativeResidual g χ (r • x)) =ᶠ[𝓝 z] r • f := by
    have hncont : Continuous (fun x : E => ‖r • x‖) := (continuous_id.const_smul r).norm
    have hsmall : ∀ᶠ x in 𝓝 z, ‖r • x‖ < χ.rIn :=
      hncont.continuousAt.eventually (Iio_mem_nhds hnorm)
    filter_upwards [hsmall, eventually_ne_nhds hz] with x hx hx0
    change r ^ 2 * nativeResidual g χ (r • x) = r * scaledDensityResidual ρ V (r, x)
    rw [nativeResidual_eq_densityResidual_inner g χ hx,
      scaledDensityResidual_eq hρ.1 hρ.2 hzero hr hx0]
    ring
  have hweq : (fun x => r ^ 2 * ρ (r • x) * nativeResidual g χ (r • x)) =ᶠ[𝓝 z] r • w := by
    filter_upwards [heq] with x hx
    change r ^ 2 * nativeResidual g χ (r • x) = r * f x at hx
    change r ^ 2 * ρ (r • x) * nativeResidual g χ (r • x) =
      r * (ρ (r • x) * f x)
    nlinarith [congrArg (fun t : ℝ => ρ (r • x) * t) hx]
  have hf : ContDiffAt ℝ ∞ f z :=
    (hF (r, z) hz).comp z (contDiffAt_const.prodMk contDiffAt_id)
  have hw : ContDiffAt ℝ ∞ w z :=
    (hW (r, z) hz).comp z (contDiffAt_const.prodMk contDiffAt_id)
  have transfer (a b : E → ℝ) (hab : a =ᶠ[𝓝 z] r • b)
      (hb : ContDiffAt ℝ ∞ b z) (hbound : ‖iteratedFDeriv ℝ n b z‖ ≤ C) :
      ‖iteratedFDeriv ℝ n a z‖ ≤ C * r := by
    rw [(hab.iteratedFDeriv ℝ n).self_of_nhds,
      iteratedFDeriv_const_smul_apply (hb.of_le (by exact_mod_cast le_top))]
    have hnorm' : ‖r • iteratedFDeriv ℝ n b z‖ = r * ‖iteratedFDeriv ℝ n b z‖ := by
      convert! norm_smul_of_nonneg hr.le (iteratedFDeriv ℝ n b z)
    rw [hnorm']
    exact (mul_le_mul_of_nonneg_left hbound hr.le).trans_eq (mul_comm r C)
  exact ⟨transfer _ _ heq hf ((hb1 n hn r ⟨hr.le, hr1⟩ z hzlo hzup).trans (le_max_left _ _)),
    transfer _ _ hweq hw ((hb2 n hn r ⟨hr.le, hr1⟩ z hzlo hzup).trans (le_max_right _ _))⟩

#print axioms exists_uniform_native_scaledResidual_jet_bounds

end Yamabe3.Analysis.GreenParametrix
