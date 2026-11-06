import Yamabe3.Analysis.C2PrincipalErrorPointwise
import Yamabe3.Analysis.NativePrincipalErrorContinuity

/-! The source value-coordinate estimate is proved as well as the H2 row
estimate. It is uniform up to the puncture and the full radius-three collar. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

def halfEndSourceCompactAnnulus : Set E := {x | (3/4:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 3/2}

theorem halfEndSourceCompactAnnulus_isCompact : IsCompact halfEndSourceCompactAnnulus := by
  apply (isCompact_closedBall (0:E) (3/2)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [mem_closedBall,dist_zero_right] using hx.2

theorem halfEndSourceCompactAnnulus_subset_basic : halfEndSourceCompactAnnulus ⊆ halfEndBasicAnnulus := by
  intro x hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem exists_uniform_H4_graph_two_jet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex)
      (j : ℕ), j ≤ 2 → ∀ x ∈ halfEndSourceCompactAnnulus,
      ‖iteratedFDeriv ℝ j (halfEndWeightedPhysicalSliceMap v.1.1 i) x‖ ≤ C*‖v‖ := by
  obtain ⟨C,hC,hb⟩ := exists_weak_H4_two_jet_bound_on_compact
    halfEndSourceCompactAnnulus_isCompact halfEndBasicAnnulus_isOpen halfEndSourceCompactAnnulus_subset_basic
  refine ⟨C.toReal+1,by positivity,?_⟩
  intro v i j hj x hx
  have hh := (hb _ _ (v.2 i).1 (halfEndWeightedPhysicalSliceMap_contDiffOn_two v i).continuousOn
    (EventuallyEq.refl _ _) j hj x hx).trans
      (mul_le_mul le_rfl (halfEndWeightedPhysicalSliceMap_norm_le v i) zero_le zero_le)
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hh
  rw [ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg v)] at hr
  exact hr.trans (by nlinarith [norm_nonneg v])

theorem exists_uniform_native_principal_error_value_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ, (g p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (g p).pullbackVolumeDensity id 0 = 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ p ∈ Λ,
      ∀ (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance),
      ‖nativeNormalizedPrincipalError (g p) ε
        (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x‖ ≤ τ*‖v‖ := by
  obtain ⟨C,hC,hjet⟩ := exists_uniform_H4_graph_two_jet_bound
  let B := Real.exp (Real.log 2/2)
  have hBpos : 0 < B := Real.exp_pos _
  let η := τ/(12*B*C)
  have hη : 0 < η := div_pos hτ (by positivity)
  obtain ⟨δ,hδ,hd⟩ := exists_uniform_small_native_geometric_error Λ g hB hρ
    (show (0:ℝ) < 2 by norm_num) (show 0 < 91*η by positivity)
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro ε hε hεδ p hp v x
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
  have hcoeff := hd (ε*r) (mul_nonneg hε hr.le) hεδ' p hp
  have hzball : z ∈ closedBall (0:E) 2 := by simpa only [mem_closedBall,dist_zero_right] using hz2
  have hA (j k : Fin 3) : ‖nativeScaledPrincipalError (g p) (ε*r) j k z‖ ≤ η := by
    simpa only [norm_iteratedFDeriv_zero,show (91:ℝ)*η/91=η by ring] using hcoeff.1 0 (by omega) z hzball j k
  have hD (j : Fin 3) : ‖nativeScaledFirstError (g p) (ε*r) j z‖ ≤ η := by
    simpa only [norm_iteratedFDeriv_zero,show (91:ℝ)*η/91=η by ring] using hcoeff.2.1 0 (by omega) z hzball j
  let U := halfEndWeightedPhysicalSliceMap v.1.1 i
  have hUC := halfEndWeightedPhysicalSliceMap_contDiffOn_two v i
  have hb := nativePrincipalError_pointwise_bound (g p) (ε*r)
    (hUC.contDiffAt (halfEndBasicAnnulus_isOpen.mem_nhds (halfEndSourceCompactAnnulus_subset_basic hz)))
    hη.le hA hD (fun j hj => hjet v i j hj z hz)
  change ‖nativePrincipalError (g p) (ε*r) (fun y => Real.exp (3*s/2)*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) (Real.exp (-s) • y)) z‖ ≤ 12*η*(C*‖v‖) at hb
  rw [he] at hb
  have hid := nativeNormalizedPrincipalError_slice (g p) ε s
    (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) hz0
  rw [hzx,he] at hid
  have hnorm : radialScale ‖z‖ * ‖nativeNormalizedPrincipalError (g p) ε
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x‖ ≤ 12*η*(C*‖v‖) := by
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
    _ ≤ (radialScale ‖z‖)⁻¹ * (12*η*(C*‖v‖)) := ha
    _ ≤ B*(12*η*(C*‖v‖)) := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = τ*‖v‖ := by dsimp only [η];field_simp [hBpos.ne',hC.ne'] <;> ring

#print axioms exists_uniform_H4_graph_two_jet_bound
#print axioms exists_uniform_native_principal_error_value_bound
end Yamabe3.Analysis.UniformElliptic
