import Yamabe3.Analysis.BoundaryFourthOrderExtension
import Yamabe3.Analysis.BoundaryLocalizedMultiplier

/-! A compact chart cutoff followed by the explicit four-sample extension
extends actual local H4 across the face with a fixed homogeneous bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def localFourthExtension (χ u : E → ℝ) : E → ℝ :=
  fourthOrderExtension (fun x => χ x * u x)

theorem localFourthExtension_eq_on {χ u : E → ℝ} {U : Set E}
    (hone : ∀ x ∈ U, χ x = 1) :
    EqOn (localFourthExtension χ u) u (U ∩ halfSpace d) := by
  intro x hx
  change fourthOrderExtension (fun y => χ y * u y) x = u x
  rw [fourthOrderExtension_eq_on _ hx.2, hone x hx.1, one_mul]

theorem exists_localFourthExtension_bound {W : Set E} (hW : IsOpen W)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp 4 2 u (W ∩ halfSpace d) →
      MemWkp 4 2 (localFourthExtension χ u) univ ∧
      iteratedWeakSobolevNorm 4 2 (localFourthExtension χ u) univ ≤
        C * iteratedWeakSobolevNorm 4 2 u (W ∩ halfSpace d) := by
  obtain ⟨A, hA, ha⟩ := exists_localized_sobolev_multiplier_bound 4 isOpen_halfSpace hW χ hχ hc hs
  obtain ⟨B, hB, hb⟩ := exists_fourthOrderExtension_bound (d := d)
  refine ⟨B*A, by finiteness, ?_⟩
  intro u hu
  have hmul := memWkp_mul_smooth_of_tsupport_subset 4 isOpen_halfSpace hW hu hχ hc hs
  have hh := hb _ hmul
  refine ⟨hh.1, hh.2.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul (a := B) le_rfl (ha u hu) zero_le zero_le

theorem localFourthExtension_add (χ u v : E → ℝ) :
    localFourthExtension χ (u+v) = localFourthExtension χ u + localFourthExtension χ v := by
  have heq : (fun x => χ x * (u+v) x) = (fun x => χ x*u x) + (fun x => χ x*v x) := by
    funext x; simp only [Pi.add_apply, mul_add]
  change fourthOrderExtension (fun x => χ x * (u+v) x) = _
  rw [heq, fourthOrderExtension_add]
  rfl

theorem localFourthExtension_smul (χ u : E → ℝ) (a : ℝ) :
    localFourthExtension χ (a • u) = a • localFourthExtension χ u := by
  have heq : (fun x => χ x * (a • u) x) = a • (fun x => χ x*u x) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  change fourthOrderExtension (fun x => χ x * (a • u) x) = _
  rw [heq, fourthOrderExtension_smul]
  rfl

#print axioms exists_localFourthExtension_bound
#print axioms localFourthExtension_eq_on
end Yamabe3.Analysis.UniformElliptic
