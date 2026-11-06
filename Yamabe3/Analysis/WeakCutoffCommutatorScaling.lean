import Yamabe3.Analysis.WeakLaplacianDilation
import Yamabe3.Analysis.WeakCutoffCommutatorBound

/-! Exact same-field weak cutoff commutator scaling. This uses genuine
weak derivative transport and uniqueness, with the literal domain and
coefficient factor; no regularity of a chosen pointwise derivative is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Sobolev.BoundaryLocalization Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

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

 theorem weakCutoffCommutator_comp_dilation
    {O:Set E} (hO:IsOpen O) {u:E→ℝ} (hu:MemWkp 1 2 u O)
    (χ:E→ℝ) {r:ℝ} (hr:r≠0) (c:ℝ):
    weakCutoffCommutator ((fun x:E=>r • x) ⁻¹' O) (fun x=>χ (r • x)) (fun x=>c*u (r • x))
      =ᵐ[volume.restrict ((fun x:E=>r • x) ⁻¹' O)]
      (fun x=>c*r^2*weakCutoffCommutator O χ u (r • x)):=by
  have hp:(1:ℝ≥0∞)≤2:=by norm_num
  have hD:=hO.preimage (continuous_const_smul r)
  have hdu:=memWkp_comp_dilation hr hO hp 1 hu
  have hd(i:Fin 3):chosenWeakPartial' 2 i (fun x=>c*u (r • x)) ((fun x:E=>r • x) ⁻¹' O)
      =ᵐ[volume.restrict ((fun x:E=>r • x) ⁻¹' O)]
      (fun x=>c*r*chosenWeakPartial' 2 i u O (r • x)):=by
    have hc:=chosenWeakPartial'_const_smul_ae hp hD hdu.memW1p c i
    have hr':=chosenWeakPartial_comp_dilation hr hO hu i
    filter_upwards [hc,hr'] with x hx hy
    change _=c*r*chosenWeakPartial' 2 i u O (r • x)
    rw [hx,hy]
    ring
  filter_upwards [eventually_all.mpr hd] with x hx
  simp only [weakCutoffCommutator,cutoff_second_comp,cutoff_partial_comp,hx,Fin.sum_univ_three]
  ring

 theorem weakCutoffCommutator_mono_set
    {O U:Set E} (hU:IsOpen U) (hsub:U⊆O) {u:E→ℝ} (hu:MemWkp 1 2 u O) (χ:E→ℝ):
    weakCutoffCommutator U χ u=ᵐ[volume.restrict U]weakCutoffCommutator O χ u:=by
  have hd(i:Fin 3):chosenWeakPartial' 2 i u U=ᵐ[volume.restrict U]chosenWeakPartial' 2 i u O:=
    (chosenWeakPartial'_mono_set_ae (by norm_num) hU hsub hu.memW1p i).symm
  filter_upwards [eventually_all.mpr hd] with x hx
  simp only [weakCutoffCommutator,hx]

#print axioms weakCutoffCommutator_comp_dilation
#print axioms weakCutoffCommutator_mono_set
end Yamabe3.Analysis.UniformElliptic
