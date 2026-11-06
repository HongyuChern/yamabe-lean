import Yamabe3.Analysis.NativeCollarCutoffCommutator

/-! Literal coordinate product rules on one open set. They are used for
the actual incoming and far cutoff commutators, with the same functions
and all cross terms retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Poincare.Analysis.Elliptic.Iteration

theorem partialDeriv_mul_at {f g:E→ℝ} {x:E} (hf:DifferentiableAt ℝ f x)
    (hg:DifferentiableAt ℝ g x) (i:Fin 3) :
    partialDeriv i (fun y=>f y*g y) x=partialDeriv i f x*g x+f x*partialDeriv i g x := by
  unfold partialDeriv
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem partialDeriv_second_mul_on {O:Set E} (hO:IsOpen O) {f g:E→ℝ}
    (hf:ContDiffOn ℝ 2 f O) (hg:ContDiffOn ℝ 2 g O) {x:E} (hx:x∈O) (i j:Fin 3) :
    partialDeriv i (partialDeriv j (fun y=>f y*g y)) x=
      partialDeriv i (partialDeriv j f) x*g x+partialDeriv j f x*partialDeriv i g x+
      partialDeriv i f x*partialDeriv j g x+f x*partialDeriv i (partialDeriv j g) x := by
  have hdf:DifferentiableAt ℝ f x := (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  have hdg:DifferentiableAt ℝ g x := (hg.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  have hjf:ContDiffOn ℝ 1 (partialDeriv j f) O :=
    (hf.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  have hjg:ContDiffOn ℝ 1 (partialDeriv j g) O :=
    (hg.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  have hdfj:DifferentiableAt ℝ (partialDeriv j f) x :=
    (hjf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  have hdgj:DifferentiableAt ℝ (partialDeriv j g) x :=
    (hjg.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  have he:partialDeriv j (fun y=>f y*g y)=ᶠ[𝓝 x]
      fun y=>partialDeriv j f y*g y+f y*partialDeriv j g y := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact partialDeriv_mul_at ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))
      ((hg.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num)) j
  change fderiv ℝ (partialDeriv j (fun y=>f y*g y)) x (EuclideanSpace.single i 1)=_
  rw [he.fderiv_eq]
  rw [fderiv_fun_add (f:=fun y:E=>partialDeriv j f y*g y) (g:=fun y:E=>f y*partialDeriv j g y) (hdfj.mul hdg) (hdf.mul hdgj)]
  change partialDeriv i (fun y=>partialDeriv j f y*g y) x+
    partialDeriv i (fun y=>f y*partialDeriv j g y) x=_
  rw [partialDeriv_mul_at hdfj hdg,partialDeriv_mul_at hdf hdgj]
  ring

#print axioms partialDeriv_mul_at
#print axioms partialDeriv_second_mul_on
end Yamabe3.Analysis.UniformElliptic
