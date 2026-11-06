import Yamabe3.Analysis.Green.NativeLocalParametrix
import PoincareLib.Analysis.Calculus.DividedDifferences
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth extension of the genuinely rescaled density residual

The vanishing first density jet removes the apparent division by the scale.
The exact integral of the actual Hessian supplies a jointly smooth extension
down to scale zero, away from the spatial origin. Compactness can therefore
give one constant for all spatial derivatives of any fixed finite order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Set MeasureTheory Metric Filter
open scoped ContDiff Topology Interval

namespace Yamabe3.Analysis.GreenParametrix

/-- The actual integrated density Hessian in the scale and spatial variables. -/
def radialDensityJet (ρ : E → ℝ) (q : ℝ × E) : ℝ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ ρ) ((t * q.1) • q.2) q.2 q.2

theorem contDiff_radialDensityJet {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (radialDensityJet ρ) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ρ)) :=
    hD.fderiv_right (by simp)
  have hF : ContDiff ℝ ∞ (fun q : (ℝ × E) × ℝ =>
      fderiv ℝ (fderiv ℝ ρ) ((q.2 * q.1.1) • q.1.2) q.1.2 q.1.2) :=
    ((hDD.comp (by fun_prop)).clm_apply (by fun_prop)).clm_apply (by fun_prop)
  exact Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff hF 0 1

/-- The actual zero first jet gives an exact second-order increment,
including its value at scale zero. -/
theorem density_jet_scaled_identity {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hzero : fderiv ℝ ρ 0 = 0) (r : ℝ) (z : E) :
    fderiv ℝ ρ (r • z) (r • z) = r ^ 2 * radialDensityJet ρ (r, z) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ρ)) := hD.fderiv_right (by simp)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => fderiv ℝ ρ ((s * r) • z) z)
      (r * fderiv ℝ (fderiv ℝ ρ) ((t * r) • z) z z) t := by
    have ht : HasDerivAt (fun s : ℝ => (s * r) • z) (r • z) t := by
      simpa only [one_mul, id_eq] using! (((hasDerivAt_id t).mul_const r).smul_const z)
    have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ ρ ((s * r) • z))
        (fderiv ℝ (fderiv ℝ ρ) ((t * r) • z) (r • z)) t :=
      ((hD.differentiable (by simp) ((t * r) • z)).hasFDerivAt).comp_hasDerivAt t ht
    have h := hcomp.clm_apply (hasDerivAt_const t z)
    simpa only [one_mul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      map_zero, add_zero, zero_add] using h
  have hc : Continuous (fun t : ℝ => r * fderiv ℝ (fderiv ℝ ρ) ((t * r) • z) z z) := by
    exact continuous_const.mul (((hDD.continuous.comp (by fun_prop)).clm_apply
      continuous_const).clm_apply continuous_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  have hi' : r * radialDensityJet ρ (r, z) = fderiv ℝ ρ (r • z) z := by
    simpa only [radialDensityJet, one_mul, zero_mul, zero_smul, hzero,
      ContinuousLinearMap.zero_apply, sub_zero] using hi
  rw [map_smul, smul_eq_mul, ← hi']
  ring

/-- The expression at zero scale is filled by the actual integrated Hessian,
not by an assumed asymptotic coefficient. -/
def scaledDensityResidual (ρ V : E → ℝ) (q : ℝ × E) : ℝ :=
  radialDensityJet ρ q / (ρ (q.1 • q.2) * ‖q.2‖ ^ 3) + V (q.1 • q.2) / ‖q.2‖

/-- Exact identification with the actual density residual at every positive
scale and every nonzero spatial coordinate. -/
theorem scaledDensityResidual_eq {ρ V : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hpos : ∀ x, 0 < ρ x) (hzero : fderiv ℝ ρ 0 = 0)
    {r : ℝ} (hr : 0 < r) {z : E} (hz : z ≠ 0) :
    scaledDensityResidual ρ V (r, z) = r * densityResidual ρ V (r • z) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hρne : ρ (r • z) ≠ 0 := (hpos _).ne'
  unfold scaledDensityResidual densityResidual
  rw [density_jet_scaled_identity hρ hzero, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  field_simp [hr.ne', hn, hρne]
  <;> ring

/-- Smoothness is joint in scale and space even at scale zero; only the
spatial origin is excluded. The density is the actual smooth positive one. -/
theorem contDiffAt_scaledDensityResidual {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) (hV : ContDiff ℝ ∞ V)
    (q : ℝ × E) (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (scaledDensityResidual ρ V) q := by
  have hn : ContDiffAt ℝ ∞ (fun p : ℝ × E => ‖p.2‖) q :=
    (contDiffAt_norm ℝ hq).comp q contDiffAt_snd
  have hρq : ContDiff ℝ ∞ (fun p : ℝ × E => ρ (p.1 • p.2)) :=
    hρ.comp (by fun_prop)
  have hVq : ContDiff ℝ ∞ (fun p : ℝ × E => V (p.1 • p.2)) :=
    hV.comp (by fun_prop)
  exact ((contDiff_radialDensityJet hρ).contDiffAt.div
    (hρq.contDiffAt.mul (hn.pow 3))
    (mul_ne_zero (hpos _).ne' (pow_ne_zero 3 (norm_ne_zero_iff.mpr hq)))).add
      (hVq.contDiffAt.div hn (norm_ne_zero_iff.mpr hq))

#print axioms contDiff_radialDensityJet
#print axioms density_jet_scaled_identity
#print axioms scaledDensityResidual_eq
#print axioms contDiffAt_scaledDensityResidual

end Yamabe3.Analysis.GreenParametrix
