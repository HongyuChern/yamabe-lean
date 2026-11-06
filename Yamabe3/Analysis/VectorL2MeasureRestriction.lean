import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! The genuine vector-valued restriction of one L2 class. This is used
for the closed lower-time-support constraint of the SAME source pair. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace X] {μ ν : Measure X} (hν : ν≤μ)

def vectorL2MeasureRestrict (F : Lp H 2 μ) : Lp H 2 ν :=
  ((Lp.memLp F).mono_measure hν).toLp (F : X → H)

theorem vectorL2MeasureRestrict_ae (F : Lp H 2 μ) :
    (vectorL2MeasureRestrict hν F : X → H)=ᵐ[ν] (F : X → H) := ((Lp.memLp F).mono_measure hν).coeFn_toLp

theorem vectorL2MeasureRestrict_norm_le (F : Lp H 2 μ) : ‖vectorL2MeasureRestrict hν F‖≤‖F‖ := by
  have h := ENNReal.toReal_mono (Lp.memLp F).2.ne (eLpNorm_mono_measure (f := (F : X → H)) (p := 2) hν)
  unfold vectorL2MeasureRestrict
  rw [Lp.norm_toLp]
  exact h

def vectorL2MeasureRestrictCLM : Lp H 2 μ →L[ℝ] Lp H 2 ν :=
  ({toFun := vectorL2MeasureRestrict hν
    map_add' := by
      intro F G
      apply Lp.ext
      filter_upwards [vectorL2MeasureRestrict_ae hν (F+G),vectorL2MeasureRestrict_ae hν F,vectorL2MeasureRestrict_ae hν G,
        ae_mono hν (Lp.coeFn_add F G),Lp.coeFn_add (vectorL2MeasureRestrict hν F) (vectorL2MeasureRestrict hν G)] with x hs hf hg hi ho
      rw [hs,ho]
      simpa only [Pi.add_apply,hf,hg] using hi
    map_smul' := by
      intro c F
      change vectorL2MeasureRestrict hν (c•F)=c•vectorL2MeasureRestrict hν F
      apply Lp.ext
      filter_upwards [vectorL2MeasureRestrict_ae hν (c•F),vectorL2MeasureRestrict_ae hν F,
        ae_mono hν (Lp.coeFn_smul c F),Lp.coeFn_smul c (vectorL2MeasureRestrict hν F)] with x hs hf hi ho
      rw [hs,ho]
      simpa only [Pi.smul_apply,smul_eq_mul,hf] using hi
    } : Lp H 2 μ →ₗ[ℝ] Lp H 2 ν).mkContinuous 1
      (by intro F;change ‖vectorL2MeasureRestrict hν F‖≤1*‖F‖;simpa only [one_mul] using vectorL2MeasureRestrict_norm_le hν F)

#print axioms vectorL2MeasureRestrict_ae
#print axioms vectorL2MeasureRestrict_norm_le
#print axioms vectorL2MeasureRestrictCLM
end Yamabe3.Analysis.UniformElliptic
