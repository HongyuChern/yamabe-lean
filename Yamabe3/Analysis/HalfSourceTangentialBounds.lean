import Yamabe3.Analysis.HalfSourceTangentialJets
import Yamabe3.Analysis.WeakLaplacianSobolev

/-! Quantitative L2 bounds for the actual first and second tangential
derivative witnesses of a source that may jump across the flat face. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_twoSidedHalfSource_le {f g : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d))) :
    eLpNorm (twoSidedHalfSource f g) 2 volume ≤
      eLpNorm f 2 (volume.restrict (halfSpace d))+eLpNorm g 2 (volume.restrict (halfSpace d)) := by
  have hfI := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hf
  have hgR := memLp_reflectedSample 1 (by norm_num) hg
  have hh := eLpNorm_add_le hfI.aestronglyMeasurable hgR.aestronglyMeasurable (by norm_num : (1:ℝ≥0∞)≤2)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict isOpen_halfSpace.measurableSet] at hh
  apply hh.trans
  apply add_le_add le_rfl
  simpa using eLpNorm_reflectedSample_le 1 (by norm_num) hg

theorem twoSidedHalfSource_first_norm_le {f g : E → ℝ}
    (hf : MemWkp 1 2 f (halfSpace d)) (hg : MemWkp 1 2 g (halfSpace d))
    (k : Fin d) (O : Set E) :
    iteratedWeakSobolevNorm 0 2
      (twoSidedHalfSource (chosenWeakPartial' 2 k f (halfSpace d))
        (chosenWeakPartial' 2 k g (halfSpace d))) O ≤
      iteratedWeakSobolevNorm 1 2 f (halfSpace d)+iteratedWeakSobolevNorm 1 2 g (halfSpace d) := by
  rw [wkpNorm_zero]
  apply (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
  apply (eLpNorm_twoSidedHalfSource_le (hf.chosenWeakPartial_mem k).memLp (hg.chosenWeakPartial_mem k).memLp).trans
  simpa only [wkpNorm_zero] using add_le_add (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 f (halfSpace d) k)
    (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 g (halfSpace d) k)

theorem twoSidedHalfSource_second_norm_le {f g : E → ℝ}
    (hf : MemWkp 2 2 f (halfSpace d)) (hg : MemWkp 2 2 g (halfSpace d))
    (k s : Fin d) (O : Set E) :
    iteratedWeakSobolevNorm 0 2
      (twoSidedHalfSource (chosenWeakPartial' 2 s (chosenWeakPartial' 2 k f (halfSpace d)) (halfSpace d))
        (chosenWeakPartial' 2 s (chosenWeakPartial' 2 k g (halfSpace d)) (halfSpace d))) O ≤
      iteratedWeakSobolevNorm 2 2 f (halfSpace d)+iteratedWeakSobolevNorm 2 2 g (halfSpace d) := by
  exact (twoSidedHalfSource_first_norm_le (hf.chosenWeakPartial_mem k) (hg.chosenWeakPartial_mem k) s O).trans
    (add_le_add (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 f (halfSpace d) k)
      (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 g (halfSpace d) k))

#print axioms eLpNorm_twoSidedHalfSource_le
#print axioms twoSidedHalfSource_first_norm_le
#print axioms twoSidedHalfSource_second_norm_le
end Yamabe3.Analysis.UniformElliptic
