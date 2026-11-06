import Yamabe3.Analysis.UniformElliptic.LocalUniformSupJet
import Yamabe3.Analysis.UniformElliptic.NativeScaledCoefficients
import Yamabe3.Analysis.UniformElliptic.LocalDivergenceEquation
import Yamabe3.Analysis.UniformElliptic.JetScaling
import Yamabe3.Analysis.UniformElliptic.NativeScaledForcing

/-!
# Genuine pointwise jets of the native Green correction

All ellipticity, coefficient and source constants are constructed uniformly
for the actual rescaled metric. A cutoff supplies the globally smooth
extensions needed by the estimates. The true native PDE is converted to its
actual weak divergence equation. Thus a half-Holder value estimate upgrades
to every fixed positive-order weighted jet estimate, for the same function
and the same native metric. The Green construction supplies the remaining
local native PDE and value estimate; they are explicit hypotheses here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
open Yamabe3.Analysis.GreenParametrix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private def annulusO : Set E3 := {z | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2}
private def annulusV : Set E3 := {z | (3 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 3 / 2}

private theorem annulusO_open : IsOpen annulusO :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

private theorem annulusV_open : IsOpen annulusV :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

private theorem annulusV_closure_bound {z : E3} (hz : z ∈ closure annulusV) :
    (3 / 4 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2 := by
  have hclosed : IsClosed {z : E3 | (3 / 4 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hs : annulusV ⊆ {z : E3 | (3 / 4 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2} :=
    fun _ h => ⟨h.1.le, h.2.le⟩
  exact closure_minimal hs hclosed hz

private theorem annulusV_precompact : IsCompact (closure annulusV) := by
  apply (isCompact_closedBall (0 : E3) 3).of_isClosed_subset isClosed_closure
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  exact (annulusV_closure_bound hz).2.trans (by norm_num)

private theorem annulusV_closure_subset : closure annulusV ⊆ annulusO := by
  intro z hz
  have h := annulusV_closure_bound hz
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem annulusV_closure_ball : closure annulusV ⊆ ball (0 : E3) 3 := by
  intro z hz
  rw [mem_ball, dist_zero_right]
  have h := (annulusV_closure_bound hz).2
  linarith

private theorem unitSphere_subset_annulusV : sphere (0 : E3) 1 ⊆ annulusV := by
  intro z hz
  have hn : ‖z‖ = 1 := by simpa using hz
  change (3 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 3 / 2
  rw [hn]
  norm_num

/-- A genuine local native correction equation and its pointwise Holder
value bound imply the same function's weighted higher jets. All rescaled
ellipticity, coefficient bounds, source bounds and smooth extensions are
proved internally; no scale-dependent estimate is assumed. -/
theorem exists_native_correction_weighted_jet_bound
    (g : RiemannianMetric 3 E3)
    (hB : g.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (g.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E3))
    {R : ℝ} (hR : 0 < R) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball (0 : E3) R \ {0}))
    (hP : ∀ y ∈ ball (0 : E3) R \ {0},
      -g.leviCivitaData.laplacian u y +
        (g.leviCivitaData.scalarCurvature y / 8) * u y = nativeResidual g χ y)
    (b H : ℝ) (hH : 0 ≤ H)
    (hholder : ∀ y ∈ ball (0 : E3) R \ {0}, ‖u y - b‖ ≤ H * ‖y‖ ^ (1 / 2 : ℝ))
    (m : ℕ) (hm : m ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x : E3, 0 < ‖x‖ → ‖x‖ < δ →
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ m u x‖ ≤ C * ‖x‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨δa, hδa, L, hL, hBa⟩ :=
    exists_uniform_native_rescaled_bilinear_forms g hB hρ (m + 4) (by norm_num : (0 : ℝ) < 3)
  obtain ⟨δf, Cf, Q, hδf, hCf, hQ, hfj⟩ :=
    exists_uniform_native_centered_forcing_jets g hzero χ (m + 2) b
  obtain ⟨A, hA, hest⟩ := exists_local_uniform_sup_jet_bound m annulusO_open
    annulusV_open annulusV_precompact annulusV_closure_subset annulusV_closure_ball
    (isCompact_sphere (0 : E3) 1) unitSphere_subset_annulusV
    (by norm_num : (0 : ℝ) < 1 / 2) hL hQ
  let δ := min 1 (min δa (min δf (R / 2)))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min hδa (lt_min hδf (by positivity)))
  have hpow : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨δ, A * (H * (2 : ℝ) ^ (1 / 2 : ℝ) + Cf), hδ,
    mul_nonneg hA (add_nonneg (mul_nonneg hH hpow) hCf), ?_⟩
  have hscaled (r : ℝ) (hr : 0 < r) (hrδ : r < δ) (z : E3)
      (hz : z ∈ sphere (0 : E3) 1) :
      ‖iteratedFDeriv ℝ m (fun y => u (r • y) - b) z‖ ≤
        (A * (H * (2 : ℝ) ^ (1 / 2 : ℝ) + Cf)) * r ^ (1 / 2 : ℝ) := by
    have hr1 : r ≤ 1 := (hrδ.trans_le (min_le_left _ _)).le
    have hra : r < δa := hrδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hrf : r < δf := hrδ.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hrR : r * 2 < R := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp
      (hrδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hmap : MapsTo (fun y : E3 => r • y) annulusO (ball (0 : E3) R \ {0}) := by
      intro y hy
      have hy0 : y ≠ 0 := by intro heq; norm_num [annulusO, heq] at hy
      refine ⟨?_, smul_ne_zero hr.ne' hy0⟩
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_lt_mul_of_pos_left hy.2 hr).trans hrR
    obtain ⟨B, hBaEq, hBlam, hBj, hBosc⟩ := hBa r hr.le hra
    have hBκ : (1 / 2 : ℝ) ≤ B.lam := by rw [hBlam]
    have hBV : annulusV ⊆ ball (0 : E3) 3 := subset_closure.trans annulusV_closure_ball
    have hBj' : ∀ n ≤ m + 1 + 3, ∀ y ∈ annulusV, ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ n (fun w => B.a w i j) y‖ ≤ L := by
      intro n hn y hy i j
      exact hBj n (by omega) y (hBV hy) i j
    have hBosc' : ∀ y ∈ annulusV, (∑ i : Fin 3, ∑ j : Fin 3,
        (B.a y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ^ 2) ≤ 1 / 4 :=
      fun y hy => hBosc y (hBV hy)
    have hj (n : ℕ) (hn : n ≤ m + 3 - 1) (y : E3) (hy : y ∈ annulusV) :=
      hfj n (by omega) r hr hrf y (by linarith [hy.1]) (by linarith [hy.2])
    have hus : ContDiffOn ℝ ∞ (fun y : E3 => u (r • y) - b) annulusO :=
      (hu.comp (contDiff_id.const_smul r).contDiffOn hmap).sub contDiffOn_const
    have hfs : ContDiffOn ℝ ∞ (centeredRescaledForcing g χ r b) annulusO := by
      intro y hy
      apply (contDiffAt_centeredRescaledForcing g χ hr.ne' b ?_).contDiffWithinAt
      intro heq
      norm_num [annulusO, heq] at hy
    have hweak : WeakEquation annulusV
        (matrixFlux B.a (fun j => partialDeriv j (fun y => u (r • y) - b)))
        (fun y => centeredRescaledForcing g χ r b y +
          rescaledCorrectionPotential g r y * (u (r • y) - b)) := by
      rw [hBaEq]
      have hn := weakEquation_rescaled_native_solution g g.leviCivitaData
        (isOpen_ball.sdiff isClosed_singleton) annulusO_open annulusV_open
        annulusV_precompact annulusV_closure_subset hu hP r b hmap
      convert! hn using 1
      funext y
      simp only [centeredRescaledForcing, rescaledCorrectionPotential, nativePotentialDensity]
      ring
    have hrhalf : r ≤ r ^ (1 / 2 : ℝ) :=
      Real.self_le_rpow_of_le_one hr.le hr1 (by norm_num)
    have hvalue (y : E3) (hy : y ∈ annulusV) :
        ‖u (r • y) - b‖ ≤ (H * (2 : ℝ) ^ (1 / 2 : ℝ)) * r ^ (1 / 2 : ℝ) := by
      have hyO := annulusV_closure_subset (subset_closure hy)
      have h := hholder (r • y) (hmap hyO)
      rw [norm_smul, Real.norm_of_nonneg hr.le,
        Real.mul_rpow hr.le (norm_nonneg y)] at h
      apply h.trans
      have hyP : ‖y‖ ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) (by linarith [hy.2]) (by norm_num)
      have hs := mul_le_mul_of_nonneg_left hyP
        (mul_nonneg hH (Real.rpow_nonneg hr.le (1 / 2 : ℝ)))
      nlinarith [hs]
    have hfjet (n : ℕ) (hn : n ≤ m + 3 - 1) (y : E3) (hy : y ∈ annulusV) :
        ‖iteratedFDeriv ℝ n (centeredRescaledForcing g χ r b) y‖ ≤ Cf * r ^ (1 / 2 : ℝ) :=
      ((hj n hn y hy).2).trans (mul_le_mul_of_nonneg_left hrhalf hCf)
    have he := hest B hBκ hBj' hBosc' (rescaledCorrectionPotential g r)
      (contDiff_rescaledCorrectionPotential g r) (fun n hn y hy => (hj n hn y hy).1)
      hus hfs hweak ((H * (2 : ℝ) ^ (1 / 2 : ℝ)) * r ^ (1 / 2 : ℝ))
      (Cf * r ^ (1 / 2 : ℝ)) (by positivity) (by positivity) hvalue hfjet z hz
    convert! he using 1 <;> ring
  intro x hx hxδ
  let r := ‖x‖
  let z : E3 := r⁻¹ • x
  have hr : 0 < r := hx
  have hnorm : ‖z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    exact inv_mul_cancel₀ hr.ne'
  have hz : z ∈ sphere (0 : E3) 1 := by simpa using hnorm
  have heq : r • z = x := by simp [z, smul_smul, hr.ne']
  have hxR : x ∈ ball (0 : E3) R \ {0} := by
    refine ⟨?_, norm_pos_iff.mp hx⟩
    rw [mem_ball, dist_zero_right]
    have hxR2 : ‖x‖ < R / 2 := hxδ.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have h := hscaled r hr hxδ z hz
  rw [norm_iteratedFDeriv_local_centered_dilation
    (isOpen_ball.sdiff isClosed_singleton) hu m hm hr.le b z (heq.symm ▸ hxR), heq] at h
  exact h

#print axioms exists_native_correction_weighted_jet_bound

end Yamabe3.Analysis.UniformElliptic
