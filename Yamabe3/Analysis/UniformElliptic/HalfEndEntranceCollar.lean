import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalCompatibility
import Yamabe3.Analysis.UniformElliptic.JetScaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The actual normalized entrance collar

A short negative logarithmic interval is controlled by the same physical
entrance slice on a larger annulus. The proof uses the native derivative
profile, an actual change of variables in Lebesgue measure, and exact jet
scaling. It does not extend a half-line function by arbitrary whole-line data.
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

/-- Dilation by at least one decreases the pushforward of Euclidean volume.
The determinant factor is proved by the actual Haar change of variables. -/
theorem map_volume_dilation_le {r : ℝ} (hr : 1 ≤ r) :
    Measure.map (fun x : E3 => r • x) volume ≤ (volume : Measure E3) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Measure.map_addHaar_smul volume hr0.ne']
  have hc : ENNReal.ofReal |(r ^ Module.finrank ℝ E3)⁻¹| ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left' hc

/-- Pullback of an actual function under an expanding dilation, restricted
to a set whose image lies in Gamma. No integrand regularity is suppressed. -/
theorem eLpNorm_dilation_le {Ω Γ : Set E3} {r : ℝ} (hr : 1 ≤ r)
    (himage : ∀ x ∈ Ω, r • x ∈ Γ) (f : E3 → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x : E3 => f (r • x)) p (volume.restrict Ω) ≤
      eLpNorm f p (volume.restrict Γ) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have he : MeasurableEmbedding (fun x : E3 => r • x) :=
    (Homeomorph.smulOfNeZero r hr0.ne').measurableEmbedding
  have hm : Measure.map (fun x : E3 => r • x) (volume.restrict Ω) ≤
      (volume : Measure E3).restrict Γ := by
    calc
      _ ≤ Measure.map (fun x : E3 => r • x)
          (volume.restrict ((fun x : E3 => r • x) ⁻¹' Γ)) :=
        Measure.map_mono (Measure.restrict_mono_set volume himage) he.measurable
      _ = (Measure.map (fun x : E3 => r • x) volume).restrict Γ :=
        (he.restrict_map volume Γ).symm
      _ ≤ _ := Measure.restrict_mono_measure (map_volume_dilation_le hr) Γ
  change eLpNorm (f ∘ (fun x : E3 => r • x)) p (volume.restrict Ω) ≤ _
  rw [← he.eLpNorm_map_measure]
  exact eLpNorm_mono_measure f hm

/-- Exact all-order norm scaling at a point where the original function is
smooth. The zero jet is included; no extension across the pole is needed. -/
theorem norm_iteratedFDeriv_scalar_local_dilation
    {O : Set E3} (hO : IsOpen O) {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (n : ℕ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) (x : E3) (hx : r • x ∈ O) :
    ‖iteratedFDeriv ℝ n (fun y : E3 => c * u (r • y)) x‖ =
      |c| * r ^ n * ‖iteratedFDeriv ℝ n u (r • x)‖ := by
  have hun : ContDiffAt ℝ n u (r • x) :=
    (hu.contDiffAt (hO.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  have hcomp : ContDiffAt ℝ n (fun y : E3 => u (r • y)) x :=
    hun.comp x (contDiff_id.const_smul r).contDiffAt
  have hout : ‖iteratedFDeriv ℝ n (fun y : E3 => c * u (r • y)) x‖ =
      |c| * ‖iteratedFDeriv ℝ n (fun y : E3 => u (r • y)) x‖ := by
    change ‖iteratedFDeriv ℝ n (c • (fun y : E3 => u (r • y))) x‖ = _
    rw [iteratedFDeriv_const_smul_apply hcomp, norm_smul, Real.norm_eq_abs]
  rw [hout]
  by_cases hn : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one]
  · rw [show ‖iteratedFDeriv ℝ n (fun y : E3 => u (r • y)) x‖ =
        r ^ n * ‖iteratedFDeriv ℝ n u (r • x)‖ by
      simpa only [sub_zero] using
        norm_iteratedFDeriv_local_centered_dilation hO hu n hn hr 0 x hx]
    ring

/-- A true local profile estimate under an expanding dilation. The factor
r^k is deliberately an upper bound; the actual volume factor is controlled
by map_volume_dilation_le rather than discarded by a change of norm. -/
theorem derivativeProfile_scalar_dilation_le
    {O Ω Γ : Set E3} (hO : IsOpen O) (hΩ : MeasurableSet Ω)
    (hΓO : Γ ⊆ O) {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    (k : ℕ) (c : ℝ) {r : ℝ} (hr : 1 ≤ r)
    (himage : ∀ x ∈ Ω, r • x ∈ Γ) :
    derivativeProfile 2 Ω k (fun x : E3 => c * u (r • x)) ≤
      ENNReal.ofReal (|c| * r ^ k) * derivativeProfile 2 Γ k u := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hc0 : 0 ≤ |c| * r ^ k := mul_nonneg (abs_nonneg _) (pow_nonneg hr0 _)
  unfold derivativeProfile
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ eLpNorm (fun x : E3 => (|c| * r ^ k) *
        ‖iteratedFDeriv ℝ j u (r • x)‖) 2 (volume.restrict Ω) := by
      apply eLpNorm_mono_ae_real
      filter_upwards [ae_restrict_mem hΩ] with x hx
      rw [norm_norm, norm_iteratedFDeriv_scalar_local_dilation hO hu j c hr0 x
        (hΓO (himage x hx))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hjk) (abs_nonneg _))
        (norm_nonneg _)
    _ = ENNReal.ofReal (|c| * r ^ k) *
        eLpNorm (fun x : E3 => ‖iteratedFDeriv ℝ j u (r • x)‖) 2
          (volume.restrict Ω) := by
      change eLpNorm ((|c| * r ^ k) •
        (fun x : E3 => ‖iteratedFDeriv ℝ j u (r • x)‖)) 2 (volume.restrict Ω) = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc0]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (eLpNorm_dilation_le hr himage (fun x : E3 => ‖iteratedFDeriv ℝ j u x‖) 2) zero_le

/-- One fixed physical entrance slice controls the genuine short negative
collar. In order four the displayed constant is 32. The enlarged annulus
and normalized physical slice both remain explicit in the conclusion. -/
theorem halfEnd_entrance_collar_unweighted_profile_le
    {ε : ℝ} (hε : 0 < ε) {O Ω Γ : Set E3}
    (hO : IsOpen O) (hΩ : MeasurableSet Ω) (hΓO : Γ ⊆ O)
    (hΩann : ∀ z ∈ Ω, (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2)
    (hΓann : {z : E3 | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 4} ⊆ Γ)
    (w : E3 → ℝ) (hw : ContDiffOn ℝ ∞ (halfEndCoordinateCorrection ε w 0) O)
    (k : ℕ) {s : ℝ} (hs : -(Real.log 2) ≤ s) (hs0 : s ≤ 0) :
    derivativeProfile 2 Ω k (halfEndCoordinateCorrection ε w s) ≤
        ENNReal.ofReal (2 ^ (k + 1) : ℝ) *
          derivativeProfile 2 Γ k (halfEndCoordinateCorrection ε w 0) := by
  have hr1 : 1 ≤ Real.exp (-s) := Real.one_le_exp_iff.mpr (by linarith)
  have hr2 : Real.exp (-s) ≤ 2 := by
    have he : Real.exp (-s) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hc2 : Real.exp (-s / 2) ≤ 2 := by
    exact (Real.exp_le_exp.mpr (by linarith : -s / 2 ≤ -s)).trans hr2
  have himage : ∀ z ∈ Ω, Real.exp (-s) • z ∈ Γ := by
    intro z hz
    apply hΓann
    change (1 / 2 : ℝ) ≤ ‖Real.exp (-s) • z‖ ∧ ‖Real.exp (-s) • z‖ ≤ 4
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hz0 := (hΩann z hz).1
    have hz2 := (hΩann z hz).2
    constructor
    · exact hz0.trans (by nlinarith [norm_nonneg z] : ‖z‖ ≤ Real.exp (-s) * ‖z‖)
    · nlinarith [norm_nonneg z]
  have heq : halfEndCoordinateCorrection ε w s = fun z : E3 =>
      Real.exp (-s / 2) * halfEndCoordinateCorrection ε w 0 (Real.exp (-s) • z) := by
    funext z
    simpa only [zero_add] using halfEndCoordinateCorrection_shift hε w 0 s z
  have hprofile := derivativeProfile_scalar_dilation_le hO hΩ hΓO hw k
    (Real.exp (-s / 2)) hr1 himage
  rw [← heq] at hprofile
  have hcoeff : |Real.exp (-s / 2)| * Real.exp (-s) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
    rw [abs_of_pos (Real.exp_pos _), pow_succ]
    calc
      _ ≤ 2 * 2 ^ k := mul_le_mul hc2
        (pow_le_pow_left₀ (Real.exp_pos _).le hr2 k) (by positivity) (by norm_num)
      _ = _ := by ring
  exact hprofile.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal hcoeff) zero_le)

/-- The same collar estimate with the actual half-end weight included. -/
theorem halfEnd_entrance_collar_profile_le
    {ε : ℝ} (hε : 0 < ε) {O Ω Γ : Set E3}
    (hO : IsOpen O) (hΩ : MeasurableSet Ω) (hΓO : Γ ⊆ O)
    (hΩann : ∀ z ∈ Ω, (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2)
    (hΓann : {z : E3 | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 4} ⊆ Γ)
    (w : E3 → ℝ) (hw : ContDiffOn ℝ ∞ (halfEndCoordinateCorrection ε w 0) O)
    (k : ℕ) {s : ℝ} (hs : -(Real.log 2) ≤ s) (hs0 : s ≤ 0) :
    ENNReal.ofReal (Real.exp (2 * s)) *
      derivativeProfile 2 Ω k (halfEndCoordinateCorrection ε w s) ≤
        ENNReal.ofReal (2 ^ (k + 1) : ℝ) *
          derivativeProfile 2 Γ k (halfEndCoordinateCorrection ε w 0) := by
  have hweight : ENNReal.ofReal (Real.exp (2 * s)) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by linarith))
  exact (mul_le_of_le_one_left' hweight).trans
    (halfEnd_entrance_collar_unweighted_profile_le hε hO hΩ hΓO hΩann hΓann w hw k hs hs0)

#print axioms map_volume_dilation_le
#print axioms eLpNorm_dilation_le
#print axioms norm_iteratedFDeriv_scalar_local_dilation
#print axioms derivativeProfile_scalar_dilation_le
#print axioms halfEnd_entrance_collar_unweighted_profile_le
#print axioms halfEnd_entrance_collar_profile_le

end Yamabe3.Analysis.UniformElliptic
