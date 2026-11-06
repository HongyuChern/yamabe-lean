import Yamabe3.Analysis.OrderedTwoScaleFeedback

/-! The physical gluing q-chi_in*R uses the NEGATIVE incoming source
return. Its bound is unchanged, while the actual fixed equation retains
the sign. This prevents a norm-only sign ambiguity in PDE assembly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology NNReal
namespace Yamabe3.Analysis.UniformElliptic
variable {X H:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_two_scale_negative_return_feedback
    (A:X →L[ℝ] X) (I:H →L[ℝ] X) (R:X →L[ℝ] H)
    (Ci N Ccut Cgeo a S:ℝ) (hCi:0 ≤ Ci) (hN:0 ≤ N) (ha:0 < a)
    (hA:‖A‖ ≤ 2) (hI:‖I‖ ≤ Ci*Real.exp (-Real.log a/2))
    (hR:‖R‖ ≤ N*Real.sqrt a*(Ccut*Real.exp (S/2)+Cgeo*a))
    (hfar:Ci*N*Ccut*Real.exp (S/2) ≤ 1/8)
    (hsmall:Ci*N*Cgeo*a ≤ 1/8) :
    ∃T:X →L[ℝ] X,‖T‖ ≤ 4 ∧ ∀f:X,A (f-I (R (T f)))=T f := by
  obtain ⟨T,hT,hTv⟩:=exists_two_scale_preconditioned_feedback A (-I) R Ci N Ccut Cgeo a S
    hCi hN ha hA (by simpa only [norm_neg] using hI) hR hfar hsmall
  refine ⟨T,hT,fun f=>?_⟩
  simpa only [ContinuousLinearMap.neg_apply,sub_eq_add_neg] using hTv f

#print axioms exists_two_scale_negative_return_feedback
end Yamabe3.Analysis.UniformElliptic
