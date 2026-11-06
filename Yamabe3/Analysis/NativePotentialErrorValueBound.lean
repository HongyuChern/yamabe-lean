import Yamabe3.Analysis.NativePotentialErrorRows
import Yamabe3.Analysis.NativePrincipalErrorValueBound

/-! Actual bounded source values for the scalar/density defect, uniformly
before orbit and phase. No pointwise value is read from a free L2 class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_native_potential_error_value_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hρ : ∀ p ∈ Λ, (g p).pullbackVolumeDensity id 0 = 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ p ∈ Λ,
      ∀ (κ : ℝ) (D : DelaunayPhaseData κ) (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance),
      ‖nativeNormalizedPotentialError (g p) ε D.orbit D.phase
        (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x‖ ≤ τ*‖v‖ := by
  obtain ⟨C,hC,hjet⟩ := exists_uniform_H4_graph_two_jet_bound
  let B := Real.exp (Real.log 2/2)
  have hBpos : 0 < B := Real.exp_pos _
  let η := τ/(B*C)
  have hη : 0 < η := div_pos hτ (by positivity)
  obtain ⟨δ,hδ,hd⟩ := exists_uniform_small_finite_native_delaunay_potential_error Λ g hρ 0 hη
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro ε hε hεδ p hp κ D v x
  let r := min ‖(x:E)‖ 2
  have hxn : 0 < ‖(x:E)‖ := norm_pos_iff.mpr x.2.1
  have hr : 0 < r := lt_min hxn (by norm_num)
  have hr2 : r ≤ 2 := min_le_right _ _
  let s := -Real.log r
  have hs : -Real.log 2 ≤ s := neg_le_neg (Real.log_le_log hr hr2)
  let i : HalfEndPhysicalSliceIndex := ⟨s,hs⟩
  let z := r⁻¹ • (x:E)
  have he : Real.exp (-s) = r := by dsimp only [s];rw [neg_neg,Real.exp_log hr]
  have hzx : Real.exp (-s) • z = (x:E) := by rw [he];dsimp only [z];rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hz : z ∈ halfEndSourceCompactAnnulus := by
    change (3/4:ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3/2
    dsimp only [z]
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le]
    by_cases hx2 : ‖(x:E)‖ ≤ 2
    · have hh : r = ‖(x:E)‖ := min_eq_left hx2
      rw [hh,inv_mul_cancel₀ hxn.ne']
      norm_num
    · have hh : r = 2 := min_eq_right (le_of_not_ge hx2)
      rw [hh]
      constructor <;> nlinarith [x.2.2,lt_of_not_ge hx2]
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith [hz.1])
  have hz2 : ‖z‖ ≤ 2 := by linarith [hz.2]
  have hεδ' : ε*r < δ := by nlinarith
  have hcoeff := hd (ε*r) (mul_nonneg hε hr.le) hεδ' p hp D.orbit D.smooth
    (fun t => ⟨(D.bounded t).1,(D.bounded t).2,D.derivative_bound t⟩) D.ode (D.phase+s)
  have hc : ‖nativeDelaunayPotentialError (g p) (ε*r) D.orbit (D.phase+s) z‖ ≤ η := by
    simpa only [norm_iteratedFDeriv_zero] using hcoeff 0 le_rfl z (by linarith [hz.1]) hz2
  have hU : ‖halfEndWeightedPhysicalSliceMap v.1.1 i z‖ ≤ C*‖v‖ := by
    simpa only [norm_iteratedFDeriv_zero] using hjet v i 0 (by omega) z hz
  have hb : ‖nativeDelaunayPotentialError (g p) (ε*r) D.orbit (D.phase+s) z *
      halfEndWeightedPhysicalSliceMap v.1.1 i z‖ ≤ η*(C*‖v‖) := by
    rw [norm_mul]
    exact mul_le_mul hc hU (norm_nonneg _) hη.le
  change ‖nativeDelaunayPotentialError (g p) (ε*r) D.orbit (D.phase+s) z *
    (Real.exp (3*s/2)*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) (Real.exp (-s) • z))‖ ≤ η*(C*‖v‖) at hb
  rw [he,show r • z = (x:E) from by rw [← he];exact hzx] at hb
  have hid := nativeNormalizedPotentialError_slice (g p) ε s D.orbit D.phase
    (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) hz0
  rw [hzx,he] at hid
  have hnorm : radialScale ‖z‖ * ‖nativeNormalizedPotentialError (g p) ε D.orbit D.phase
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x‖ ≤ η*(C*‖v‖) := by
    have hh := congrArg norm hid
    rw [norm_mul,Real.norm_of_nonneg (radialScale_pos _).le] at hh
    exact hh.trans_le hb
  have hinv : (radialScale ‖z‖)⁻¹ ≤ B := by
    unfold radialScale
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hh := Real.log_le_log (norm_pos_iff.mpr hz0) hz2
    linarith
  have ha := mul_le_mul_of_nonneg_left hnorm (inv_pos.mpr (radialScale_pos ‖z‖)).le
  rw [← mul_assoc,inv_mul_cancel₀ (radialScale_pos _).ne',one_mul] at ha
  calc
    _ ≤ (radialScale ‖z‖)⁻¹ * (η*(C*‖v‖)) := ha
    _ ≤ B*(η*(C*‖v‖)) := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = τ*‖v‖ := by dsimp only [η];field_simp [hBpos.ne',hC.ne'] <;> ring


#print axioms exists_uniform_native_potential_error_value_bound
end Yamabe3.Analysis.UniformElliptic
