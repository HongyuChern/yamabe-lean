import Yamabe3.Analysis.LocalPartialProductRules
import Yamabe3.Analysis.NativeC2GeometricError

/-! Exact density-divergence cutoff identity. All first coefficient
terms and both mixed product terms are retained for one same field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def densityCutoffCommutator (A:E→Matrix (Fin 3) (Fin 3) ℝ) (χ u:E→ℝ) (x:E) : ℝ :=
  (∑i:Fin 3,∑j:Fin 3,A x i j*(partialDeriv i (partialDeriv j χ) x*u x+
    partialDeriv j χ x*partialDeriv i u x+partialDeriv i χ x*partialDeriv j u x))+
  ∑j:Fin 3,(∑i:Fin 3,partialDeriv i (fun y=>A y i j) x)*partialDeriv j χ x*u x

theorem densityCutoffCommutator_eq_principal_difference
    (A:E→Matrix (Fin 3) (Fin 3) ℝ) (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j))
    {O:Set E} (hO:IsOpen O) {χ u:E→ℝ} (hχ:ContDiffOn ℝ 2 χ O)
    (hu:ContDiffOn ℝ 2 u O) {x:E} (hx:x∈O) :
    densityCutoffCommutator A χ u x=
      χ x*principalSource A u x-principalSource A (fun y=>χ y*u y) x := by
  let b:Fin 3→E→ℝ := fun j y=>∑i:Fin 3,partialDeriv i (fun z=>A z i j) y
  have huAt:ContDiffAt ℝ 2 u x := hu.contDiffAt (hO.mem_nhds hx)
  have hχAt:ContDiffAt ℝ 2 χ x := hχ.contDiffAt (hO.mem_nhds hx)
  have h1:=principalSource_eq_secondOrderOperator_C2_at b hA x huAt
  have h2:=principalSource_eq_secondOrderOperator_C2_at b hA x (hχAt.mul huAt)
  have hb (j:Fin 3):b j x-∑i:Fin 3,partialDeriv i (fun y=>A y i j) x=0 := sub_self _
  simp only [hb,zero_mul,Finset.sum_const_zero,add_zero] at h1 h2
  rw [h1,h2]
  unfold densityCutoffCommutator secondOrderOperator
  simp only [partialDeriv_second_mul_on hO hχ hu hx,
    partialDeriv_mul_at (hχAt.differentiableAt (by norm_num)) (huAt.differentiableAt (by norm_num)),b,
    Fin.sum_univ_three]
  ring

theorem densityCutoffCommutator_eq_negative_local_source
    (A:E→Matrix (Fin 3) (Fin 3) ℝ) (hA:∀i j,ContDiff ℝ ∞ (fun x=>A x i j))
    {O:Set E} (hO:IsOpen O) {χ u:E→ℝ} (hχ:ContDiffOn ℝ 2 χ O)
    (hu:ContDiffOn ℝ 2 u O) (S:E→ℝ) {x:E} (hx:x∈O)
    (hzero:principalSource A u x+S x*u x=0) :
    densityCutoffCommutator A χ u x=
      -(principalSource A (fun y=>χ y*u y) x+S x*(χ x*u x)) := by
  rw [densityCutoffCommutator_eq_principal_difference A hA hO hχ hu hx]
  nlinarith [congrArg (fun z:ℝ=>χ x*z) hzero]

#print axioms densityCutoffCommutator_eq_principal_difference
#print axioms densityCutoffCommutator_eq_negative_local_source
end Yamabe3.Analysis.UniformElliptic
