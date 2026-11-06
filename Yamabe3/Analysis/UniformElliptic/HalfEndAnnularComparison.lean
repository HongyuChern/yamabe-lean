import Yamabe3.Analysis.UniformElliptic.HalfEndAnnularMeasure

/-!
# Larger-annulus control from the same physical half-end and its entrance

The larger annulus is covered by an inner piece, the original annulus,
and an outer piece. Exact physical compatibility shifts the first and last
pieces by log 2. Only the short negative collar is charged to the entrance.
The resulting constants are explicit and independent of the entrance scale.

The theorem is stated for smooth physical coordinate functions away from
zero. It is a genuine classical-profile estimate, not an assertion of
Sobolev density or of a globally coupled inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

def halfEndBasicAnnulus : Set E3 := {z | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2}
def halfEndLargerAnnulus : Set E3 := {z | (1 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 4}
def halfEndEntranceAnnulus : Set E3 := {z | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 4}
private def innerPiece : Set E3 := {z | (1 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 1}
private def outerPiece : Set E3 := {z | (1 : ℝ) < ‖z‖ ∧ ‖z‖ < 4}

private theorem punctured_open : IsOpen {z : E3 | z ≠ 0} :=
  isOpen_ne

theorem halfEndCoordinateCorrection_contDiffOn_punctured
    {ε : ℝ} (hε : 0 < ε) {w : E3 → ℝ}
    (hw : ContDiffOn ℝ ∞ w {z : E3 | z ≠ 0}) (s : ℝ) :
    ContDiffOn ℝ ∞ (halfEndCoordinateCorrection ε w s) {z : E3 | z ≠ 0} := by
  have heq : halfEndCoordinateCorrection ε w s = fun z : E3 =>
      (radialScale (ε * Real.exp (-s)))⁻¹ * w ((ε * Real.exp (-s)) • z) := rfl
  rw [heq]
  refine contDiffOn_const.mul (hw.comp (contDiff_id.const_smul _).contDiffOn ?_)
  intro z hz
  exact smul_ne_zero (mul_pos hε (Real.exp_pos _)).ne' hz

private theorem basic_annulus_open : IsOpen halfEndBasicAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

private theorem basic_annulus_nonzero : halfEndBasicAnnulus ⊆ {z : E3 | z ≠ 0} := by
  intro z hz
  apply norm_pos_iff.mp
  change (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2 at hz
  linarith [hz.1]

private theorem entrance_annulus_nonzero : halfEndEntranceAnnulus ⊆ {z : E3 | z ≠ 0} := by
  intro z hz
  apply norm_pos_iff.mp
  change (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 4 at hz
  linarith [hz.1]

private theorem profile_inner_piece_le {ε : ℝ} (hε : 0 < ε) {w : E3 → ℝ}
    (hw : ContDiffOn ℝ ∞ w {z : E3 | z ≠ 0}) (s : ℝ) :
    derivativeProfile 2 innerPiece 4 (halfEndCoordinateCorrection ε w s) ≤
      32 * derivativeProfile 2 halfEndBasicAnnulus 4
        (halfEndCoordinateCorrection ε w (s + Real.log 2)) := by
  have hA : IsOpen innerPiece :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have himage : ∀ z ∈ innerPiece, (2 : ℝ) • z ∈ halfEndBasicAnnulus := by
    intro z hz
    change (1 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 1 at hz
    change (1 / 2 : ℝ) < ‖(2 : ℝ) • z‖ ∧ ‖(2 : ℝ) • z‖ < 2
    rw [norm_smul, show ‖(2 : ℝ)‖ = 2 by norm_num]
    constructor <;> nlinarith [hz.1, hz.2]
  have heq : halfEndCoordinateCorrection ε w s = fun z : E3 =>
      Real.exp (Real.log 2 / 2) *
        halfEndCoordinateCorrection ε w (s + Real.log 2) ((2 : ℝ) • z) := by
    funext z
    have h := halfEndCoordinateCorrection_shift hε w (s + Real.log 2) (-(Real.log 2)) z
    rw [show s + Real.log 2 + -(Real.log 2) = s by ring, neg_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  have hb := derivativeProfile_scalar_dilation_le punctured_open hA.measurableSet
    basic_annulus_nonzero (halfEndCoordinateCorrection_contDiffOn_punctured hε hw (s + Real.log 2))
      4 (Real.exp (Real.log 2 / 2)) (by norm_num : (1 : ℝ) ≤ 2) himage
  rw [← heq] at hb
  have hc : Real.exp (Real.log 2 / 2) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr
      (show Real.log 2 / 2 ≤ Real.log 2 by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh
  have hcoef : ENNReal.ofReal (|Real.exp (Real.log 2 / 2)| * (2 : ℝ) ^ 4) ≤ 32 := by
    have hh : |Real.exp (Real.log 2 / 2)| * (2 : ℝ) ^ 4 ≤ 32 := by
      rw [abs_of_pos (Real.exp_pos _)]
      norm_num at hc ⊢
      linarith
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hh
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef zero_le)

private theorem profile_outer_piece_le {ε : ℝ} (hε : 0 < ε) {w : E3 → ℝ}
    (hw : ContDiffOn ℝ ∞ w {z : E3 | z ≠ 0}) (s : ℝ) :
    derivativeProfile 2 outerPiece 4 (halfEndCoordinateCorrection ε w s) ≤
      8 * derivativeProfile 2 halfEndBasicAnnulus 4
        (halfEndCoordinateCorrection ε w (s - Real.log 2)) := by
  have hA : IsOpen outerPiece :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have himage : ∀ z ∈ outerPiece, (1 / 2 : ℝ) • z ∈ halfEndBasicAnnulus := by
    intro z hz
    change (1 : ℝ) < ‖z‖ ∧ ‖z‖ < 4 at hz
    change (1 / 2 : ℝ) < ‖(1 / 2 : ℝ) • z‖ ∧ ‖(1 / 2 : ℝ) • z‖ < 2
    rw [norm_smul, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
    constructor <;> nlinarith [hz.1, hz.2]
  have hexp : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have heq : halfEndCoordinateCorrection ε w s = fun z : E3 =>
      Real.exp (-(Real.log 2) / 2) *
        halfEndCoordinateCorrection ε w (s - Real.log 2) ((1 / 2 : ℝ) • z) := by
    funext z
    have h := halfEndCoordinateCorrection_shift hε w (s - Real.log 2) (Real.log 2) z
    rw [sub_add_cancel, hexp] at h
    exact h
  have hc : |Real.exp (-(Real.log 2) / 2)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hb := derivativeProfile_scalar_half_dilation_le punctured_open hA.measurableSet
    basic_annulus_nonzero (halfEndCoordinateCorrection_contDiffOn_punctured hε hw (s - Real.log 2))
      4 hc himage
  simpa only [← heq] using hb

private theorem halfEnd_weight_log_two (s : ℝ) :
    ENNReal.ofReal (Real.exp (2 * (s + Real.log 2))) =
      4 * ENNReal.ofReal (Real.exp (2 * s)) := by
  have he : Real.exp (2 * Real.log 2) = (4 : ℝ) := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show 2 * (s + Real.log 2) = 2 * s + 2 * Real.log 2 by ring,
    Real.exp_add, he, ENNReal.ofReal_mul (Real.exp_pos _).le]
  norm_num only [ENNReal.ofReal_ofNat]
  ring

/-- The larger actual H4 annulus needed for interior nonlinear estimates
is controlled by the same physical half-end norm and one actual entrance
profile. The finite cover includes the intermediate sphere and uses the
correct three-dimensional contraction Jacobian. -/
theorem halfEndDerivativeProfile_large_annulus_le {ε : ℝ} (hε : 0 < ε) {w : E3 → ℝ}
    (hw : ContDiffOn ℝ ∞ w {z : E3 | z ≠ 0}) :
    halfEndDerivativeProfile halfEndLargerAnnulus 4 (halfEndCoordinateCorrection ε w) ≤
      41 * halfEndDerivativeProfile halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w) +
        1024 * derivativeProfile 2 halfEndEntranceAnnulus 4 (halfEndCoordinateCorrection ε w 0) := by
  let N := halfEndDerivativeProfile halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w)
  let B := derivativeProfile 2 halfEndEntranceAnnulus 4 (halfEndCoordinateCorrection ε w 0)
  have hN (s : ℝ) (hs : 0 ≤ s) : ENNReal.ofReal (Real.exp (2 * s)) *
      derivativeProfile 2 halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w s) ≤ N :=
    le_iSup₂_of_le s hs le_rfl
  have hcover : halfEndLargerAnnulus ⊆ (innerPiece ∪ halfEndBasicAnnulus) ∪ outerPiece := by
    intro z hz
    change (1 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 4 at hz
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · exact Or.inl (Or.inl ⟨hz.1, hlt⟩)
    · exact Or.inl (Or.inr (by
        change (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2
        rw [heq]
        norm_num))
    · exact Or.inr ⟨hgt, hz.2⟩
  have hcoverProfile (s : ℝ) : derivativeProfile 2 halfEndLargerAnnulus 4
      (halfEndCoordinateCorrection ε w s) ≤
        derivativeProfile 2 innerPiece 4 (halfEndCoordinateCorrection ε w s) +
          derivativeProfile 2 halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w s) +
            derivativeProfile 2 outerPiece 4 (halfEndCoordinateCorrection ε w s) := by
    exact (derivativeProfile_mono_set hcover 2 4 (halfEndCoordinateCorrection ε w s)).trans
      ((derivativeProfile_union_le (innerPiece ∪ halfEndBasicAnnulus) outerPiece
        (halfEndCoordinateCorrection ε w s) 4).trans
          (add_le_add (derivativeProfile_union_le innerPiece halfEndBasicAnnulus
            (halfEndCoordinateCorrection ε w s) 4) le_rfl))
  change (⨆ s : ℝ, ⨆ (_hs : 0 ≤ s), ENNReal.ofReal (Real.exp (2 * s)) *
    derivativeProfile 2 halfEndLargerAnnulus 4 (halfEndCoordinateCorrection ε w s)) ≤ 41 * N + 1024 * B
  refine iSup_le fun s => iSup_le fun hs => ?_
  have hinner : ENNReal.ofReal (Real.exp (2 * s)) *
      derivativeProfile 2 innerPiece 4 (halfEndCoordinateCorrection ε w s) ≤ 8 * N := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (2 * s)) * (32 * derivativeProfile 2 halfEndBasicAnnulus 4
          (halfEndCoordinateCorrection ε w (s + Real.log 2))) :=
        mul_le_mul_of_nonneg_left (profile_inner_piece_le hε hw s) zero_le
      _ = 8 * (ENNReal.ofReal (Real.exp (2 * (s + Real.log 2))) *
          derivativeProfile 2 halfEndBasicAnnulus 4
            (halfEndCoordinateCorrection ε w (s + Real.log 2))) := by
        rw [halfEnd_weight_log_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hN (s + Real.log 2) (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])) zero_le
  have hshift : ENNReal.ofReal (Real.exp (2 * (s - Real.log 2))) *
      derivativeProfile 2 halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w (s - Real.log 2)) ≤
        N + 32 * B := by
    by_cases ht : 0 ≤ s - Real.log 2
    · exact (hN (s - Real.log 2) ht).trans le_self_add
    · have hc := halfEnd_entrance_collar_profile_le hε punctured_open basic_annulus_open.measurableSet
        entrance_annulus_nonzero (fun z hz => ⟨hz.1.le, hz.2.le⟩)
        (show {z : E3 | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 4} ⊆ halfEndEntranceAnnulus from subset_rfl)
        w (halfEndCoordinateCorrection_contDiffOn_punctured hε hw 0) 4
        (show -(Real.log 2) ≤ s - Real.log 2 by linarith)
        (le_of_not_ge ht)
      norm_num only [show (2 : ℝ) ^ (4 + 1) = 32 by norm_num, ENNReal.ofReal_ofNat] at hc
      exact hc.trans le_add_self
  have houter : ENNReal.ofReal (Real.exp (2 * s)) *
      derivativeProfile 2 outerPiece 4 (halfEndCoordinateCorrection ε w s) ≤
        32 * N + 1024 * B := by
    have hwgt : ENNReal.ofReal (Real.exp (2 * s)) =
        4 * ENNReal.ofReal (Real.exp (2 * (s - Real.log 2))) := by
      simpa only [sub_add_cancel] using halfEnd_weight_log_two (s - Real.log 2)
    calc
      _ ≤ ENNReal.ofReal (Real.exp (2 * s)) * (8 * derivativeProfile 2 halfEndBasicAnnulus 4
          (halfEndCoordinateCorrection ε w (s - Real.log 2))) :=
        mul_le_mul_of_nonneg_left (profile_outer_piece_le hε hw s) zero_le
      _ = 32 * (ENNReal.ofReal (Real.exp (2 * (s - Real.log 2))) *
          derivativeProfile 2 halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w (s - Real.log 2))) := by
        rw [hwgt]
        ring
      _ ≤ 32 * (N + 32 * B) := mul_le_mul_of_nonneg_left hshift zero_le
      _ = _ := by ring
  calc
    _ ≤ ENNReal.ofReal (Real.exp (2 * s)) *
        (derivativeProfile 2 innerPiece 4 (halfEndCoordinateCorrection ε w s) +
          derivativeProfile 2 halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w s) +
            derivativeProfile 2 outerPiece 4 (halfEndCoordinateCorrection ε w s)) :=
      mul_le_mul_of_nonneg_left (hcoverProfile s) zero_le
    _ = ENNReal.ofReal (Real.exp (2 * s)) *
          derivativeProfile 2 innerPiece 4 (halfEndCoordinateCorrection ε w s) +
        ENNReal.ofReal (Real.exp (2 * s)) *
          derivativeProfile 2 halfEndBasicAnnulus 4 (halfEndCoordinateCorrection ε w s) +
        ENNReal.ofReal (Real.exp (2 * s)) *
          derivativeProfile 2 outerPiece 4 (halfEndCoordinateCorrection ε w s) := by ring
    _ ≤ 8 * N + N + (32 * N + 1024 * B) := add_le_add (add_le_add hinner (hN s hs)) houter
    _ = _ := by ring

#print axioms halfEndCoordinateCorrection_contDiffOn_punctured
#print axioms halfEndDerivativeProfile_large_annulus_le

end Yamabe3.Analysis.UniformElliptic
