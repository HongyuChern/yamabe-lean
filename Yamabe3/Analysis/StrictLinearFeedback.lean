import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.Contracting

/-! A bounded linear plus-feedback solver with the actual strict gap q<1.
The norm records its denominator, including the low-mode q=7/8 case. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology NNReal
namespace Yamabe3.Analysis.UniformElliptic
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

 theorem strictFeedback_contracting (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (f : Y) :
    ContractingWith q (fun u : X => T (f+A u)) := by
  refine ⟨hq,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm,dist_eq_norm,←map_sub]
  have he : (f+A u)-(f+A v)=A (u-v) := by rw [map_sub];abel
  rw [he]
  calc
    _ ≤ ‖T‖*(‖A‖*‖u-v‖) := (T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg T))
    _ ≤ q*‖u-v‖ := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)

def strictFeedbackSolution (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (f : Y) : X :=
  (strictFeedback_contracting T A hq hsmall f).fixedPoint (fun u => T (f+A u))

theorem strictFeedback_fixed (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (f : Y) :
    T (f+A (strictFeedbackSolution T A hq hsmall f))=strictFeedbackSolution T A hq hsmall f :=
  (strictFeedback_contracting T A hq hsmall f).fixedPoint_isFixedPt

theorem strictFeedback_unique (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (f : Y) (u : X) (hu : T (f+A u)=u) :
    strictFeedbackSolution T A hq hsmall f=u :=
  ((strictFeedback_contracting T A hq hsmall f).fixedPoint_unique hu).symm

theorem strictFeedback_norm (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (f : Y) :
    ‖strictFeedbackSolution T A hq hsmall f‖≤(‖T‖/(1-(q:ℝ)))*‖f‖ := by
  let u := strictFeedbackSolution T A hq hsmall f
  have he := strictFeedback_fixed T A hq hsmall f
  have hn : ‖u‖≤‖T‖*‖f‖+(q:ℝ)*‖u‖ := by
    calc
      _ = ‖T (f+A u)‖ := congrArg norm he.symm
      _ ≤ ‖T‖*‖f+A u‖ := T.le_opNorm _
      _ ≤ ‖T‖*(‖f‖+‖A‖*‖u‖) := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add le_rfl (A.le_opNorm _))) (norm_nonneg T)
      _ ≤ _ := by rw [mul_add,←mul_assoc];exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (norm_nonneg u))
  have hpos : 0<1-(q:ℝ) := sub_pos.mpr (by exact_mod_cast hq)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  dsimp only [u] at hn ⊢
  nlinarith

theorem strictFeedback_add (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (f g : Y) :
    strictFeedbackSolution T A hq hsmall (f+g)=
      strictFeedbackSolution T A hq hsmall f+strictFeedbackSolution T A hq hsmall g := by
  apply strictFeedback_unique
  rw [map_add A]
  have he : (f+g)+(A (strictFeedbackSolution T A hq hsmall f)+A (strictFeedbackSolution T A hq hsmall g))=
      (f+A (strictFeedbackSolution T A hq hsmall f))+(g+A (strictFeedbackSolution T A hq hsmall g)) := by abel
  rw [he,map_add,strictFeedback_fixed,strictFeedback_fixed]

theorem strictFeedback_smul (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) (c : ℝ) (f : Y) :
    strictFeedbackSolution T A hq hsmall (c • f)=c • strictFeedbackSolution T A hq hsmall f := by
  apply strictFeedback_unique
  rw [map_smul,←smul_add,map_smul,strictFeedback_fixed]

def strictFeedbackCLM (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) : Y →L[ℝ] X :=
  LinearMap.mkContinuous
    {toFun := strictFeedbackSolution T A hq hsmall
     map_add' := strictFeedback_add T A hq hsmall
     map_smul' := strictFeedback_smul T A hq hsmall}
    (‖T‖/(1-(q:ℝ))) (strictFeedback_norm T A hq hsmall)

theorem strictFeedbackCLM_norm (T : Y →L[ℝ] X) (A : X →L[ℝ] Y)
    {q : ℝ≥0} (hq : q<1) (hsmall : ‖T‖*‖A‖≤q) :
    ‖strictFeedbackCLM T A hq hsmall‖≤‖T‖/(1-(q:ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (norm_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hq.le))) (strictFeedback_norm T A hq hsmall)

#print axioms strictFeedback_fixed
#print axioms strictFeedback_unique
#print axioms strictFeedback_norm
#print axioms strictFeedback_add
#print axioms strictFeedback_smul
#print axioms strictFeedbackCLM_norm
end Yamabe3.Analysis.UniformElliptic
