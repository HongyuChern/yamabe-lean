import Yamabe3.Analysis.NativeGlobalCutoffCommutator
import Yamabe3.Analysis.NativePhysicalCutoffSourceIdentity

/-! The actual fixed-scale physical cutoff source equals the same
unscaled weak commutator, with its exact factor8 and true derivative
support. The annulus indicator is removed by a proved support statement. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Elliptic.Iteration

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

 theorem nativeScaledCutoffCommutator_zero_off_shell
    (χ u:E→ℝ) (S:ℝ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    {x:E} (hx:x∉nativeScaledSourceShell S):
    weakCutoffCommutator univ (fun y=>χ (Real.exp S • y)) u x=0:=by
  have hxs:Real.exp S • x∉nativeSourceShell:=hx
  simp only [weakCutoffCommutator,cutoff_second_comp,cutoff_partial_comp,
    (hs _ hxs _).1,(hs _ hxs _).2,mul_zero,zero_mul,add_zero,Finset.sum_const_zero,neg_zero]

 theorem nativePhysicalCutoffSource_global_commutator
    {u:E→ℝ} (hu:MemWkp 1 2 u univ) (χ:E→ℝ) (S:ℝ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0):
    physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation S u) S 1=ᵐ[volume]
      (fun x=>8*weakCutoffCommutator univ (fun y=>χ (Real.exp S • y)) u x):=by
  have hwu:MemWkp 1 2 (weightedPhysicalDilation S u) univ:=by
    have hd:=memWkp_comp_dilation (Real.exp_ne_zero (-S)) isOpen_univ (by norm_num:(1:ℝ≥0∞)≤2) 1 hu
    simp only [preimage_univ] at hd
    exact MemWkp.const_smul (by norm_num) isOpen_univ hd (Real.exp (3*S/2))
  have hloc:=weakCutoffCommutator_mono_set halfEndBasicAnnulus_isOpen (subset_univ _) hwu χ
  have he:halfEndBasicAnnulus.indicator (weakCutoffCommutator halfEndBasicAnnulus χ (weightedPhysicalDilation S u))
      =ᵐ[volume]weakCutoffCommutator univ χ (weightedPhysicalDilation S u):=by
    have h:=(ae_restrict_iff' halfEndBasicAnnulus_isOpen.measurableSet).mp hloc
    filter_upwards [h] with x hx
    by_cases ho:x∈halfEndBasicAnnulus
    · rw [indicator_of_mem ho,hx ho]
    · rw [indicator_of_notMem ho]
      symm
      apply weakCutoffCommutator_zero_of_derivative_support univ χ _ hs
      exact fun hxs=>ho (nativeSourceShell_subset_collar.trans
        (subset_closure.trans nativeEntranceCollar_closure_subset_basic) hxs)
  have hd:=ae_comp_dilation (Real.exp_ne_zero S) (ae_restrict_of_ae (s:=univ) he)
  simp only [preimage_univ,Measure.restrict_univ] at hd
  have ht:=nativeWeightedCutoffCommutator_physical hu χ S S
  have hχid:nativeOuterFieldCutoffAtScale S S χ=χ:=by
    funext x
    simp only [nativeOuterFieldCutoffAtScale,sub_self,Real.exp_zero,one_smul]
  rw [hχid] at ht
  filter_upwards [hd,ht] with x hx ht
  have hf:physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation S u) S 1 x=
      8*Real.exp (S/2)*(halfEndBasicAnnulus.indicator
        (weakCutoffCommutator halfEndBasicAnnulus χ (weightedPhysicalDilation S u))) (Real.exp S • x):=by
    unfold physicalCutoffSource physicalCutoffAnnulus
    simp only [Real.log_one,mul_zero,neg_zero,sub_zero,zero_add]
    by_cases ho:Real.exp S • x∈halfEndBasicAnnulus
    · rw [indicator_of_mem ho,indicator_of_mem (show x∈(fun y:E=>Real.exp S • y) ⁻¹' halfEndBasicAnnulus from ho)]
    · rw [indicator_of_notMem ho,indicator_of_notMem (show x∉(fun y:E=>Real.exp S • y) ⁻¹' halfEndBasicAnnulus from ho),mul_zero]
  rw [hf,hx]
  calc
    _=8*(Real.exp (S/2)*weakCutoffCommutator univ χ (weightedPhysicalDilation S u) (Real.exp S • x)):=by ring
    _=_:=by rw [ht]

#print axioms nativeScaledCutoffCommutator_zero_off_shell
#print axioms nativePhysicalCutoffSource_global_commutator
end Yamabe3.Analysis.SpherePolar
