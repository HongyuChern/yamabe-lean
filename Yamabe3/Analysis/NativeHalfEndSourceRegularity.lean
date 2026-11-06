import Yamabe3.Analysis.NativeHalfEndSourceInput
import Yamabe3.Analysis.NativeWeakDilation
import Yamabe3.Analysis.UniformElliptic.NativeDelaunayJacobianIdentity
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.LocalSobolev

/-!
# The same source graph has genuine physical local H2

Every point is placed in an actual normalized source annulus.  The weak
Sobolev dilation theorem transports that graph member's derivatives back
to physical coordinates.  Thus local H2 of the forcing is produced from
the source graph, not added to the inverse's hypotheses.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

def halfEndEuclideanPhysicalSource (f : HalfEndSourceValue) (x : E) : ℝ :=
  8 * radialScale ‖x‖ * halfEndSourceExtension f x

theorem halfEndH2SourceGraph_physical_local_H2 (f : HalfEndPhysicalH2SourceGraph) :
    MemWkpLocally 2 (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx.2
  have hx1 : ‖x‖ < 1 := by simpa using hx.1
  let s : ℝ := -Real.log ‖x‖
  have hs0 : 0 ≤ s := neg_nonneg.mpr (Real.log_nonpos (norm_nonneg x) hx1.le)
  have hs : -Real.log 2 ≤ s := (neg_nonpos.mpr (Real.log_nonneg (by norm_num))).trans hs0
  let i : HalfEndPhysicalSliceIndex := ⟨s, hs⟩
  let c := Real.exp s
  have hc : 0 < c := Real.exp_pos s
  let W : Set E := (fun y : E => c • y) ⁻¹' halfEndSourceAnnulus
  have hW : IsOpen W := halfEndSourceAnnulus_isOpen.preimage (continuous_id.const_smul c)
  have hxn : ‖c • x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg hc.le]
    dsimp only [c, s]
    rw [Real.exp_neg, Real.exp_log (norm_pos_iff.mpr hx0), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  have hxW : x ∈ W := by
    change (3 / 4 : ℝ) < ‖c • x‖ ∧ ‖c • x‖ < 3 / 2
    rw [hxn]
    norm_num
  let q := halfEndWeightedSourceSliceMap f.1.1 i
  have hq : MemWkp 2 2 (fun y : E => q (c • y)) W :=
    memWkp_comp_dilation hc.ne' halfEndSourceAnnulus_isOpen (by norm_num) 2 (f.2 i).1
  have hq' := MemWkp.const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW hq
    (8 / radialScale c)
  have heq : (fun y : E => (8 / radialScale c) * q (c • y)) =ᵐ[volume.restrict W]
      halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
    have hyn : 0 < ‖y‖ := by
      have hlo : (3 / 4 : ℝ) < ‖c • y‖ := hy.1
      by_contra h
      have hz : y = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt h) (norm_nonneg y))
      norm_num [hz] at hlo
    have hexp : Real.exp (-s) * c = 1 := by
      dsimp only [c]
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    change (8 / radialScale c) *
      (radialScale ‖c • y‖ * halfEndSourceExtension f.1.1 (Real.exp (-s) • (c • y))) =
        8 * radialScale ‖y‖ * halfEndSourceExtension f.1.1 y
    rw [norm_smul, Real.norm_of_nonneg hc.le, radialScale_mul_positive hc hyn,
      smul_smul, hexp, one_smul]
    field_simp [(radialScale_pos c).ne']
  have hphys := (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW heq).mp hq'
  exact ⟨W ∩ O, hW.inter hO, ⟨hxW, hx⟩, inter_subset_right,
    hphys.mono_set (by norm_num) (hW.inter hO) inter_subset_left⟩

theorem halfEndH2SourceGraph_forcing_local_H2 (f : HalfEndPhysicalH2SourceGraph) :
    MemWkpLocally 2 (physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) *
      halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f) p))
      (Metric.ball (0 : E) 1 \ {(0 : E)}) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWO, hreg⟩ := halfEndH2SourceGraph_physical_local_H2 f x hx
  refine ⟨W, hW, hxW, hWO, ?_⟩
  apply (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW ?_).mpr hreg
  filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
  have hyO := hWO hy
  exact halfEndSourceCylinder_physicalForcing _ (by simpa using hyO.2)
    (le_of_lt (by simpa using hyO.1))

#print axioms halfEndH2SourceGraph_physical_local_H2
#print axioms halfEndH2SourceGraph_forcing_local_H2

end Yamabe3.Analysis.UniformElliptic
