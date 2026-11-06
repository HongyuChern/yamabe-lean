import Yamabe3.Analysis.NativeHalfEndSourceRegularity
import Yamabe3.Analysis.WeakDilationNorm
import Yamabe3.Analysis.CompactFamilySobolevBound

/-! The original source graph controls its literal normalized source on
any fixed precompact annulus, uniformly at all sufficiently positive times.
Only fixed dilations and a finite geometric cover are used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

def actualWeightedSourceSlice (f : HalfEndPhysicalH2SourceGraph) (s : ℝ) (x : E) : ℝ :=
  radialScale ‖x‖ * halfEndSourceExtension (halfEndPhysicalH2SourceGraphValue f) (Real.exp (-s) • x)

theorem actualWeightedSourceSlice_shift (f : HalfEndPhysicalH2SourceGraph)
    (s : ℝ) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ≠ 0) :
    actualWeightedSourceSlice f (s+Real.log r) (r • x) =
      radialScale r * actualWeightedSourceSlice f s x := by
  unfold actualWeightedSourceSlice
  rw [norm_smul,Real.norm_of_nonneg hr.le,radialScale_mul_positive hr (norm_pos_iff.mpr hx),smul_smul]
  have he : Real.exp (-(s+Real.log r))*r = Real.exp (-s) := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log r),Real.exp_log hr]
    field_simp
  rw [he]
  ring

theorem actualWeightedSourceSlice_graph_bound (f : HalfEndPhysicalH2SourceGraph)
    (s : ℝ) (hs : -Real.log 2 ≤ s) :
    MemWkp 2 2 (actualWeightedSourceSlice f s) halfEndSourceAnnulus ∧
      iteratedWeakSobolevNorm 2 2 (actualWeightedSourceSlice f s) halfEndSourceAnnulus ≤ ENNReal.ofReal ‖f‖ := by
  let i : HalfEndPhysicalSliceIndex := ⟨s,hs⟩
  have he : actualWeightedSourceSlice f s = halfEndWeightedSourceSliceMap f.1.1 i := rfl
  rw [he]
  refine ⟨(f.2 i).1,?_⟩
  exact (ENNReal.le_ofReal_iff_toReal_le (wkpNorm_lt_top_of_memWkp (f.2 i).1).ne (norm_nonneg f)).mpr
    (weakSobolevGraph_local_norm_le halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
      halfEndWeightedSourceSliceMap f i)

theorem exists_uniform_weighted_source_precompact_bound
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hV0 : ∀ x ∈ closure V, x ≠ 0) {R : ℝ} (hR : 1 ≤ R)
    (hVR : ∀ x ∈ closure V, ‖x‖ ≤ R) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : HalfEndPhysicalH2SourceGraph) (s : ℝ), Real.log R ≤ s →
      MemWkp 2 2 (actualWeightedSourceSlice f s) V ∧
        iteratedWeakSobolevNorm 2 2 (actualWeightedSourceSlice f s) V ≤ C*ENNReal.ofReal ‖f‖ := by
  let J := HalfEndPhysicalH2SourceGraph × {s : ℝ // Real.log R ≤ s}
  let u (j : J) := actualWeightedSourceSlice j.1 j.2.1
  let B (j : J) := ENNReal.ofReal ‖j.1‖
  have hl : ∀ a ∈ closure V, ∃ (N : Set E) (C : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ C ≠ ⊤ ∧ ∀ j : J,
        MemWkp 2 2 (u j) N ∧ iteratedWeakSobolevNorm 2 2 (u j) N ≤ C*B j := by
    intro a ha
    have han : 0 < ‖a‖ := norm_pos_iff.mpr (hV0 a ha)
    let r := ‖a‖⁻¹
    have hr : 0 < r := inv_pos.mpr han
    let N := (fun x : E => r • x) ⁻¹' halfEndSourceAnnulus
    have hN : IsOpen N := halfEndSourceAnnulus_isOpen.preimage (continuous_id.const_smul r)
    have haN : a ∈ N := by
      change (3/4:ℝ) < ‖r • a‖ ∧ ‖r • a‖ < 3/2
      rw [norm_smul,Real.norm_of_nonneg hr.le]
      change (3/4:ℝ) < ‖a‖⁻¹*‖a‖ ∧ ‖a‖⁻¹*‖a‖ < 3/2
      rw [inv_mul_cancel₀ han.ne']
      norm_num
    obtain ⟨D,hD,hb⟩ := exists_weak_dilation_sobolev_bound (d := 3) 2 hr.ne'
    let c := (radialScale r)⁻¹
    refine ⟨N,ENNReal.ofReal |c| *D,haN,hN,by finiteness,?_⟩
    intro j
    have ht : -Real.log 2 ≤ j.2.1+Real.log r := by
      have hl := Real.log_le_log han (hVR a ha)
      have ht0 : 0 ≤ j.2.1+Real.log r := by
        dsimp only [r]
        rw [Real.log_inv]
        linarith [j.2.2]
      exact (neg_nonpos.mpr (Real.log_nonneg (by norm_num))).trans ht0
    let q := actualWeightedSourceSlice j.1 (j.2.1+Real.log r)
    have hq := actualWeightedSourceSlice_graph_bound j.1 _ ht
    have hc := memWkp_comp_dilation hr.ne' halfEndSourceAnnulus_isOpen (by norm_num) 2 hq.1
    have hcu := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hN hc c
    have he : (fun x => c*q (r • x)) =ᵐ[volume.restrict N] u j := by
      filter_upwards [ae_restrict_mem hN.measurableSet] with x hx
      have hx0 : x ≠ 0 := by
        intro h
        have hn : (3/4:ℝ) < ‖r • x‖ := hx.1
        norm_num [h] at hn
      change c*actualWeightedSourceSlice j.1 (j.2.1+Real.log r) (r • x) = actualWeightedSourceSlice j.1 j.2.1 x
      rw [actualWeightedSourceSlice_shift _ _ hr hx0]
      dsimp only [c]
      rw [← mul_assoc,inv_mul_cancel₀ (radialScale_pos r).ne',one_mul]
    refine ⟨(MemWkp_congr_ae (by norm_num) hN he).mp hcu,?_⟩
    rw [← wkpNorm_congr_ae (k := 2) (by norm_num) hN he,
      wkpNorm_const_smul (by norm_num) hN hc c,Real.enorm_eq_ofReal_abs]
    calc
      _ ≤ ENNReal.ofReal |c| *(D*ENNReal.ofReal ‖j.1‖) :=
        mul_le_mul le_rfl ((hb _ halfEndSourceAnnulus_isOpen q hq.1).trans
          (mul_le_mul le_rfl hq.2 zero_le zero_le)) zero_le zero_le
      _ = _ := by dsimp only [B]; ring
  obtain ⟨C,hC,hb⟩ := exists_compact_family_sobolev_bound 2 hV hVc u B hl
  exact ⟨C,hC,fun f s hs => hb (f,⟨s,hs⟩)⟩

#print axioms actualWeightedSourceSlice_shift
#print axioms actualWeightedSourceSlice_graph_bound
#print axioms exists_uniform_weighted_source_precompact_bound
end Yamabe3.Analysis.UniformElliptic
