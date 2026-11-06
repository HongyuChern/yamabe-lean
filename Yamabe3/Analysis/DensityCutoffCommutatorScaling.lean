import Yamabe3.Analysis.DensityCutoffCommutatorIdentity

/-! Exact dilation of the full density-divergence cutoff commutator.
The two mixed terms and the true coefficient derivatives all scale by
one common factor; no flat-coefficient approximation is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

private theorem cutoff_partial_comp (u:E→ℝ) (r:ℝ) (i:Fin 3) (x:E):
    partialDeriv i (fun y=>u (r • y)) x=r*partialDeriv i u (r • x):=by
  unfold partialDeriv
  rw [fderiv_comp_smul]
  simp only [smul_apply,smul_eq_mul]

private theorem cutoff_partial_const (u:E→ℝ) (c:ℝ) (i:Fin 3) (x:E):
    partialDeriv i (fun y=>c*u y) x=c*partialDeriv i u x:=by
  change fderiv ℝ (c • u) x (EuclideanSpace.single i 1)=_
  rw [fderiv_const_smul_field]
  rfl

private theorem cutoff_second_comp (u:E→ℝ) (r:ℝ) (i j:Fin 3) (x:E):
    partialDeriv i (partialDeriv j (fun y=>u (r • y))) x=
      r^2*partialDeriv i (partialDeriv j u) (r • x):=by
  have hf:partialDeriv j (fun y=>u (r • y))=fun y=>r*partialDeriv j u (r • y):=
    funext (cutoff_partial_comp u r j)
  rw [hf,cutoff_partial_const,cutoff_partial_comp]
  ring

theorem densityCutoffCommutator_dilation
    (A:E→Matrix (Fin 3) (Fin 3) ℝ) (χ u:E→ℝ) (r c:ℝ) (x:E):
    densityCutoffCommutator (fun y=>A (r • y)) (fun y=>χ (r • y))
      (fun y=>c*u (r • y)) x=c*r^2*densityCutoffCommutator A χ u (r • x):=by
  have hA(i j k:Fin 3):partialDeriv i (fun y=>A (r • y) j k) x=
      r*partialDeriv i (fun y=>A y j k) (r • x):=cutoff_partial_comp (fun y=>A y j k) r i x
  simp only [densityCutoffCommutator,cutoff_second_comp,cutoff_partial_comp,cutoff_partial_const,hA]
  simp only [Fin.sum_univ_three]
  ring

#print axioms densityCutoffCommutator_dilation
end Yamabe3.Analysis.UniformElliptic
