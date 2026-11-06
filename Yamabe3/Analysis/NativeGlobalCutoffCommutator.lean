import Yamabe3.Analysis.WeakCutoffCommutatorScaling
import Yamabe3.Analysis.NativeCollarCutoffCommutator
import Yamabe3.Analysis.NativeBCFPhysicalShellSource
import Yamabe3.Analysis.NativeOuterCutoffGeometricSender

/-! Each actual cutoff jet has the SAME unscaled physical commutator.
A global H1 field is an auxiliary local extension, not a new solution or
a new hypothesis for the original source producer. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Sobolev.BoundaryLocalization Poincare.Analysis.Elliptic.Iteration

 theorem nativeCollarCutoffCommutator_same_global_field
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (J:nativeCollarJetClosure)
    {u:E→ℝ} (hu:MemWkp 1 2 u univ)
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u):
    (nativeCollarCutoffCommutatorCLM χ hχ J.val:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weakCutoffCommutator univ χ u:=by
  have hp:(1:ℝ≥0∞)≤2:=by norm_num
  have hd(i:Fin 3):chosenWeakPartial' 2 i J.val.1 nativePoissonEntranceCollar=ᵐ[volume.restrict nativePoissonEntranceCollar]
      chosenWeakPartial' 2 i u univ:=
    (chosenWeakPartial'_ae_congr hp (nativePolarTimeWindow_open (1/2)) hJ i).trans
      (chosenWeakPartial'_mono_set_ae hp (nativePolarTimeWindow_open (1/2)) (subset_univ _) hu.memW1p i).symm
  filter_upwards [nativeCollarCutoffCommutator_ae χ hχ J,hJ,eventually_all.mpr hd] with x hx hv hd
  rw [hx]
  simp only [weakCutoffCommutator,hv,hd]

 theorem nativeWeightedCutoffCommutator_physical
    {u:E→ℝ} (hu:MemWkp 1 2 u univ) (χ:E→ℝ) (S s:ℝ):
    (fun x=>Real.exp (s/2)*weakCutoffCommutator univ
      (nativeOuterFieldCutoffAtScale S s χ) (weightedPhysicalDilation s u) (Real.exp s • x))=ᵐ[volume]
      weakCutoffCommutator univ (fun x=>χ (Real.exp S • x)) u:=by
  let χp:E→ℝ:=fun x=>χ (Real.exp S • x)
  have he:(fun x:E=>χp (Real.exp (-s) • x))=nativeOuterFieldCutoffAtScale S s χ:=by
    funext x
    simp only [χp,nativeOuterFieldCutoffAtScale,smul_smul,←Real.exp_add]
    congr 1
  have hd:=weakCutoffCommutator_comp_dilation isOpen_univ hu χp (Real.exp_ne_zero (-s)) (Real.exp (3*s/2))
  simp only [preimage_univ,he,Measure.restrict_univ] at hd
  have hd':=ae_comp_dilation (Real.exp_ne_zero s) (ae_restrict_of_ae (s:=univ) hd)
  simp only [preimage_univ,Measure.restrict_univ] at hd'
  filter_upwards [hd'] with x hx
  change Real.exp (s/2)*weakCutoffCommutator univ _ (fun y=>Real.exp (3*s/2)*u (Real.exp (-s) • y)) (Real.exp s • x)=_
  rw [hx,smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  have hc:Real.exp (s/2)*(Real.exp (3*s/2)*Real.exp (-s)^2)=1:=by
    rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
    norm_num <;> ring
  calc
    _=(Real.exp (s/2)*(Real.exp (3*s/2)*Real.exp (-s)^2))*weakCutoffCommutator univ χp u x:=by ring
    _=_:=by rw [hc,one_mul]

 theorem nativeCutoffJet_global_physical_row
    {u:E→ℝ} (hu:MemWkp 1 2 u univ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (S s:ℝ)
    (J:nativeCollarJetClosure)
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u):
    (fun x=>Real.exp (s/2)*(nativeCollarCutoffCommutatorCLM
      (nativeOuterFieldCutoffAtScale S s χ) (nativeOuterFieldCutoffAtScale_smooth S s hχ) J.val:E→ℝ) (Real.exp s • x))
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
      weakCutoffCommutator univ (fun x=>χ (Real.exp S • x)) u:=by
  have hwu:MemWkp 1 2 (weightedPhysicalDilation s u) univ:=by
    have hd:=memWkp_comp_dilation (Real.exp_ne_zero (-s)) isOpen_univ (by norm_num:(1:ℝ≥0∞)≤2) 1 hu
    simp only [preimage_univ] at hd
    exact MemWkp.const_smul (by norm_num) isOpen_univ hd (Real.exp (3*s/2))
  have hc:=nativeCollarCutoffCommutator_same_global_field (nativeOuterFieldCutoffAtScale S s χ)
    (nativeOuterFieldCutoffAtScale_smooth S s hχ) J hwu hJ
  have hd:=ae_comp_dilation (Real.exp_ne_zero s) hc
  have ht:=ae_restrict_of_ae (s:=nativePhysicalScaleWindow s) (nativeWeightedCutoffCommutator_physical hu χ S s)
  filter_upwards [hd,ht] with x hx ht
  rw [hx,ht]

 theorem nativeCutoffJet_global_shell_source
    {u:E→ℝ} (hu:MemWkp 1 2 u univ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (S s:ℝ)
    (J:nativeCollarJetClosure)
    (hJ:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u):
    nativePhysicalShellSource 1 s (nativeCollarCutoffCommutatorCLM
      (nativeOuterFieldCutoffAtScale S s χ) (nativeOuterFieldCutoffAtScale_smooth S s hχ) J.val)=ᵐ[volume]
      (fun x=>8*(nativeScaledSourceShell s).indicator
        (weakCutoffCommutator univ (fun x=>χ (Real.exp S • x)) u) x):=by
  have hsub:nativeScaledSourceShell s⊆nativePhysicalScaleWindow s:=preimage_mono nativeSourceShell_subset_collar
  have hr:=ae_mono (Measure.restrict_mono hsub le_rfl) (nativeCutoffJet_global_physical_row hu χ hχ S s J hJ)
  have hh:=(ae_restrict_iff' (nativeScaledSourceShell_measurable s)).mp hr
  filter_upwards [hh] with x hx
  by_cases hxD:x∈nativeScaledSourceShell s
  · have hxs:Real.exp s • x∈nativeSourceShell:=hxD
    simp only [nativePhysicalShellSource,Real.log_one,mul_zero,neg_zero,sub_zero,zero_add,
      nativeZeroShellSource,indicator_of_mem hxs,indicator_of_mem hxD]
    calc
      _=8*(Real.exp (s/2)*(nativeCollarCutoffCommutatorCLM
        (nativeOuterFieldCutoffAtScale S s χ) (nativeOuterFieldCutoffAtScale_smooth S s hχ) J.val:E→ℝ) (Real.exp s • x)):=by ring
      _=_:=by rw [hx hxD]
  · have hxs:Real.exp s • x∉nativeSourceShell:=hxD
    simp only [nativePhysicalShellSource,Real.log_one,mul_zero,neg_zero,sub_zero,zero_add,
      nativeZeroShellSource,indicator_of_notMem hxs,indicator_of_notMem hxD,mul_zero]

#print axioms nativeCollarCutoffCommutator_same_global_field
#print axioms nativeWeightedCutoffCommutator_physical
#print axioms nativeCutoffJet_global_physical_row
#print axioms nativeCutoffJet_global_shell_source
end Yamabe3.Analysis.SpherePolar
