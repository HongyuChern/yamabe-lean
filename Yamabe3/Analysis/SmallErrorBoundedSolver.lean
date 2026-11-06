import Yamabe3.Analysis.NativeFullTrueEntranceSolver
import Mathlib.Topology.MetricSpace.Contracting

/-! A real bounded solution of u = T(f - Eu), constructed by contraction.
The minus sign is retained for an error E = native minus model. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter
open scoped Topology NNReal
namespace Yamabe3.Analysis.UniformElliptic
variable {X Y:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem smallErrorIteration_contracting (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) (f:Y) :
    ContractingWith (1/2:ℝ≥0) (fun u:X=>T (f-E u)) := by
  refine ⟨by norm_num,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm,dist_eq_norm,←map_sub]
  have he:(f-E u)-(f-E v)= -E (u-v):=by rw [map_sub];abel
  rw [he,map_neg,norm_neg]
  calc
    _ ≤ ‖T‖*(‖E‖*‖u-v‖):=(T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (E.le_opNorm _) (norm_nonneg T))
    _ ≤ (1/2)*‖u-v‖:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
    _ = _:=by norm_num

def smallErrorSolution (T:Y→L[ℝ]X) (E:X→L[ℝ]Y) (hsmall:‖T‖*‖E‖≤1/2) (f:Y) : X :=
  (smallErrorIteration_contracting T E hsmall f).fixedPoint (fun u:X=>T (f-E u))

theorem smallErrorSolution_fixed (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) (f:Y) :
    T (f-E (smallErrorSolution T E hsmall f))=smallErrorSolution T E hsmall f :=
  (smallErrorIteration_contracting T E hsmall f).fixedPoint_isFixedPt

theorem smallErrorSolution_unique (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) (f:Y) (u:X) (hu:T (f-E u)=u) :
    smallErrorSolution T E hsmall f=u :=
  ((smallErrorIteration_contracting T E hsmall f).fixedPoint_unique hu).symm

theorem smallErrorSolution_norm_le (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) (f:Y) :
    ‖smallErrorSolution T E hsmall f‖≤(2*‖T‖)*‖f‖ := by
  let u:=smallErrorSolution T E hsmall f
  have he:=smallErrorSolution_fixed T E hsmall f
  have hn:‖u‖≤‖T‖*‖f‖+(1/2)*‖u‖:=by
    calc
      _ = ‖T (f-E u)‖:=congrArg norm he.symm
      _ ≤ ‖T‖*‖f-E u‖:=T.le_opNorm _
      _ ≤ ‖T‖*(‖f‖+‖E‖*‖u‖):=mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add le_rfl (E.le_opNorm _))) (norm_nonneg T)
      _ ≤ ‖T‖*‖f‖+(1/2)*‖u‖:=by
        rw [mul_add,←mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (norm_nonneg u))
  linarith

theorem smallErrorSolution_add (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) (f g:Y) :
    smallErrorSolution T E hsmall (f+g)=smallErrorSolution T E hsmall f+smallErrorSolution T E hsmall g := by
  apply smallErrorSolution_unique
  rw [map_add]
  have he:(f+g)-(E (smallErrorSolution T E hsmall f)+E (smallErrorSolution T E hsmall g))=
      (f-E (smallErrorSolution T E hsmall f))+(g-E (smallErrorSolution T E hsmall g)):=by abel
  rw [he,map_add,smallErrorSolution_fixed,smallErrorSolution_fixed]

theorem smallErrorSolution_smul (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) (c:ℝ) (f:Y) :
    smallErrorSolution T E hsmall (c • f)=c • smallErrorSolution T E hsmall f := by
  apply smallErrorSolution_unique
  rw [map_smul,←smul_sub,map_smul,smallErrorSolution_fixed]

def smallErrorSolutionCLM (T:Y→L[ℝ]X) (E:X→L[ℝ]Y) (hsmall:‖T‖*‖E‖≤1/2) : Y→L[ℝ]X :=
  LinearMap.mkContinuous
    {toFun:=smallErrorSolution T E hsmall
     map_add':=smallErrorSolution_add T E hsmall
     map_smul':=smallErrorSolution_smul T E hsmall}
    (2*‖T‖) (smallErrorSolution_norm_le T E hsmall)

theorem smallErrorSolutionCLM_norm (T:Y→L[ℝ]X) (E:X→L[ℝ]Y)
    (hsmall:‖T‖*‖E‖≤1/2) : ‖smallErrorSolutionCLM T E hsmall‖≤2*‖T‖ :=
  (smallErrorSolutionCLM T E hsmall).opNorm_le_bound (by positivity)
    (smallErrorSolution_norm_le T E hsmall)

#print axioms smallErrorIteration_contracting
#print axioms smallErrorSolution_fixed
#print axioms smallErrorSolution_unique
#print axioms smallErrorSolution_norm_le
#print axioms smallErrorSolution_add
#print axioms smallErrorSolution_smul
#print axioms smallErrorSolutionCLM_norm
end Yamabe3.Analysis.UniformElliptic
