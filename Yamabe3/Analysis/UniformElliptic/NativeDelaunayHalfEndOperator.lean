import Yamabe3.Analysis.UniformElliptic.NativeDelaunayJacobianIdentity

/-!
# The actual geometric error on an entire weighted half-end

The norm is the supremum of the real annular derivative profiles after
the common weight exp(2s) is applied. The small coefficient estimate is
uniform before the entrance radius, whole half-end parameter, finite
chart, actual bounded orbit and phase. It consumes H4 to control H2.
The same physical correction is normalized by the actual radialScale.
No C0 absorption, complete inverse, or free boundary solvability follows
from this estimate alone.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Delaunay
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The genuine order-k annular Sobolev profile, with weight -2 over the
entire half-end. Its finiteness is an actual property of the same family. -/
def halfEndDerivativeProfile (Ω : Set E3) (k : ℕ) (W : ℝ → E3 → ℝ) : ℝ≥0∞ :=
  ⨆ s : ℝ, ⨆ (_hs : 0 ≤ s), ENNReal.ofReal (Real.exp (2 * s)) *
    derivativeProfile 2 Ω k (W s)

/-- This is the actual correction w(r z), divided by the physical radial
conformal scale, for r=epsilon exp(-s). -/
def halfEndCoordinateCorrection (ε : ℝ) (w : E3 → ℝ) (s : ℝ) (z : E3) : ℝ :=
  (radialScale (ε * Real.exp (-s)))⁻¹ * w ((ε * Real.exp (-s)) • z)

theorem nativeRescaledDelaunayJacobian_const_mul
    (g : RiemannianMetric 3 E3) (r : ℝ) (v : ℝ → ℝ) (τ c : ℝ)
    (w : E3 → ℝ) (z : E3) :
    nativeRescaledDelaunayJacobian g r v τ (fun y => c * w y) z =
      c * nativeRescaledDelaunayJacobian g r v τ w z := by
  have hPS : principalSource (fun y => nativeDivergenceMatrix g (r • y))
      (fun y => c * w y) z =
      c * principalSource (fun y => nativeDivergenceMatrix g (r • y)) w z := by
    simpa only [one_smul, sub_zero, one_pow, mul_one, one_mul] using
      principalSource_scaled_centered (fun y => nativeDivergenceMatrix g (r • y)) w 1 c 0 z
  unfold nativeRescaledDelaunayJacobian
  rw [hPS]
  ring

/-- The normalized expression keeps the actual Jacobian, density,
coefficient eight and the physical logarithmic phase of the same w. -/
theorem halfEndCoordinateCorrection_native_jacobian
    (g : RiemannianMetric 3 E3) (v : ℝ → ℝ) (σ ε s : ℝ)
    (hε : 0 < ε) {w : E3 → ℝ} {z : E3}
    (hw : ContDiffAt ℝ ∞ w ((ε * Real.exp (-s)) • z)) (hz : z ≠ 0) :
    let r := ε * Real.exp (-s)
    nativeRescaledDelaunayJacobian g r v (σ - Real.log r)
      (halfEndCoordinateCorrection ε w s) z =
      (r ^ 2 * g.pullbackVolumeDensity id (r • z) / (8 * radialScale r)) *
        (-8 * g.leviCivitaData.laplacian w (r • z) +
          (g.leviCivitaData.scalarCurvature (r • z) -
            30 * radialProfile v σ ‖r • z‖ ^ 4) * w (r • z)) := by
  dsimp only
  unfold halfEndCoordinateCorrection
  rw [nativeRescaledDelaunayJacobian_const_mul,
    nativeRescaledDelaunayJacobian_eq_actual_native_jacobian g v σ
      (mul_pos hε (Real.exp_pos _)) hw hz]
  ring

/-- A single radius threshold controls the genuine H4-to-H2 error norm
on every point of the half-end. Arbitrary phase dependence is allowed;
no whole-line continuity of the orbit as a C_b parameter is needed. -/
theorem exists_uniform_small_half_end_delaunay_operator_error
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E3)
    (hB : ∀ p ∈ Λ, (gE p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ p ∈ Λ,
      ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ (τ : ℝ → ℝ) (O Ω : Set E3), IsOpen O → IsOpen Ω →
          IsCompact (closure Ω) → closure Ω ⊆ O → (∀ z ∈ O, z ≠ 0) →
          (∀ z ∈ Ω, (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2) →
          ∀ W : ℝ → E3 → ℝ, (∀ s, 0 ≤ s → ContDiffOn ℝ ∞ (W s) O) →
            halfEndDerivativeProfile Ω 2
              (fun s => nativeDelaunayOperatorError (gE p) (ε * Real.exp (-s))
                v (τ s) (W s)) ≤
              ENNReal.ofReal θ * halfEndDerivativeProfile Ω 4 W := by
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_local_small_native_delaunay_operator_error Λ gE hB hρ hθ
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ p hp v hv hvb hODE τ O Ω hO hΩ hΩc hΩO hO0 hΩann W hW
  unfold halfEndDerivativeProfile
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  have hr : 0 < ε * Real.exp (-s) := mul_pos hε (Real.exp_pos _)
  have hrε : ε * Real.exp (-s) ≤ ε := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -s ≤ 0)) hε.le
  have he := hb (ε * Real.exp (-s)) hr.le (hrε.trans_lt hεδ) p hp
    v hv hvb hODE (τ s) O Ω hO hΩ hΩc hΩO hO0 hΩann (W s) (hW s hs)
  have hslice : ENNReal.ofReal (Real.exp (2 * s)) * derivativeProfile 2 Ω 4 (W s) ≤
      ⨆ t : ℝ, ⨆ (_ht : 0 ≤ t), ENNReal.ofReal (Real.exp (2 * t)) *
        derivativeProfile 2 Ω 4 (W t) := by
    exact le_iSup₂_of_le s hs le_rfl
  calc
    _ ≤ ENNReal.ofReal (Real.exp (2 * s)) *
        (ENNReal.ofReal θ * derivativeProfile 2 Ω 4 (W s)) :=
      mul_le_mul_of_nonneg_left he zero_le
    _ = ENNReal.ofReal θ *
        (ENNReal.ofReal (Real.exp (2 * s)) * derivativeProfile 2 Ω 4 (W s)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      hslice zero_le

#print axioms nativeRescaledDelaunayJacobian_const_mul
#print axioms halfEndCoordinateCorrection_native_jacobian
#print axioms exists_uniform_small_half_end_delaunay_operator_error

end Yamabe3.Analysis.UniformElliptic
