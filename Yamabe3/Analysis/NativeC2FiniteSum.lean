import Yamabe3.Analysis.NativeC2SecondBudget

/-! Actual first and second partial derivatives commute with finite sums
on an open C2 domain, by differentiation of germs. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

theorem nativeCoordinateFirst_finite_sum {ι : Type*} (s : Finset ι)
    {O : Set E} (hO : IsOpen O) (u : ι → E → ℝ)
    (hu : ∀ l ∈ s, ContDiffOn ℝ 2 (u l) O)
    (i : Fin 3) {x : E} (hx : x ∈ O) :
    nativeCoordinateFirst i (fun y => ∑ l ∈ s,u l y) x =
      ∑ l ∈ s,nativeCoordinateFirst i (u l) x := by
  unfold nativeCoordinateFirst
  rw [fderiv_fun_sum (fun l hl => ((hu l hl).contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num))]
  simp only [ContinuousLinearMap.sum_apply]

theorem nativeCoordinateSecond_finite_sum {ι : Type*} (s : Finset ι)
    {O : Set E} (hO : IsOpen O) (u : ι → E → ℝ)
    (hu : ∀ l ∈ s, ContDiffOn ℝ 2 (u l) O)
    (k i : Fin 3) {x : E} (hx : x ∈ O) :
    nativeCoordinateSecond k i (fun y => ∑ l ∈ s,u l y) x =
      ∑ l ∈ s,nativeCoordinateSecond k i (u l) x := by
  have he : nativeCoordinateFirst i (fun y => ∑ l ∈ s,u l y) =ᶠ[𝓝 x]
      (fun y => ∑ l ∈ s,nativeCoordinateFirst i (u l) y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact nativeCoordinateFirst_finite_sum s hO u hu i hy
  unfold nativeCoordinateSecond
  rw [he.fderiv_eq]
  have hd (l : ι) (hl : l ∈ s) : DifferentiableAt ℝ (nativeCoordinateFirst i (u l)) x := by
    have hp : ContDiffOn ℝ 1 (nativeCoordinateFirst i (u l)) O :=
      ((hu l hl).fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
    exact (hp.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  rw [fderiv_fun_sum hd]
  simp only [ContinuousLinearMap.sum_apply,nativeCoordinateSecond]

#print axioms nativeCoordinateFirst_finite_sum
#print axioms nativeCoordinateSecond_finite_sum
end Yamabe3.Analysis.SpherePolar
