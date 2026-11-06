import Yamabe3.Analysis.NativeAllScaleCommutatorAssembly

/-! The same finite commutator assembly at the actual chart scale.
Exact logarithmic dilation retains dimension/normalization and the same
fixed-scale physical source; no new source or representative is chosen. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration

 theorem nativePhysicalShellSource_chart_scale (a s:ℝ) (U:NativeCollarL2) (x:E):
    nativePhysicalShellSource a s U x=Real.exp (-2*Real.log a)*
      nativePhysicalShellSource 1 s U (Real.exp (-Real.log a) • x):=by
  have hm:Real.exp s • (Real.exp (-Real.log a) • x)=Real.exp (s-Real.log a) • x:=by
    rw [smul_smul,←Real.exp_add]
    congr 1
  simp only [nativePhysicalShellSource,Real.log_one,mul_zero,sub_zero,zero_add,hm]
  calc
    _=8*(Real.exp (-2*Real.log a)*Real.exp (s/2))*nativeZeroShellSource U (Real.exp (s-Real.log a) • x):=by
      rw [←Real.exp_add]
    _=_:=by ring

 theorem physicalCutoffSource_chart_scale (O:Set E) (χ u:E→ℝ) (a S:ℝ) (x:E):
    physicalCutoffSource O χ u S a x=Real.exp (-2*Real.log a)*
      physicalCutoffSource O χ u S 1 (Real.exp (-Real.log a) • x):=by
  have hm:Real.exp S • (Real.exp (-Real.log a) • x)=Real.exp (S-Real.log a) • x:=by
    rw [smul_smul,←Real.exp_add]
    congr 1
  have hmem:x∈physicalCutoffAnnulus O S a ↔ Real.exp (-Real.log a) • x∈physicalCutoffAnnulus O S 1:=by
    change Real.exp (S-Real.log a) • x∈O ↔ Real.exp (S-Real.log 1) • (Real.exp (-Real.log a) • x)∈O
    rw [Real.log_one,sub_zero,hm]
  unfold physicalCutoffSource
  by_cases hx:x∈physicalCutoffAnnulus O S a
  · rw [indicator_of_mem hx,indicator_of_mem (hmem.mp hx)]
    simp only [Real.log_one,mul_zero,sub_zero,zero_add,hm]
    calc
      _=8*(Real.exp (-2*Real.log a)*Real.exp (S/2))*weakCutoffCommutator O χ u (Real.exp (S-Real.log a) • x):=by
        rw [←Real.exp_add]
      _=_:=by ring
  · rw [indicator_of_notMem hx,indicator_of_notMem (fun h=>hx (hmem.mpr h)),mul_zero]

 theorem nativeAllScale_physical_cutoff_commutator_assembly
    (J:ℝ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (a S:ℝ) (N:ℕ) (hS:S≤-(1/4:ℝ)) (hN:-S+1/4≤(N:ℝ)/2):
    (fun x:E=>∑i:Fin N,nativePhysicalShellSource a (nativeOuterLogShellCenter i)
      (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i)).val) x)=ᵐ[volume]
      physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation S u) S a:=by
  have hh:=nativeAllScale_cutoff_commutator_assembly J u hJ χ hχ hs S N hS hN
  have hd:=ae_comp_dilation (Real.exp_ne_zero (-Real.log a)) (ae_restrict_of_ae (s:=univ) hh)
  simp only [preimage_univ,Measure.restrict_univ] at hd
  filter_upwards [hd] with x hx
  simp_rw [nativePhysicalShellSource_chart_scale a]
  rw [←Finset.mul_sum,hx,←physicalCutoffSource_chart_scale]

#print axioms nativePhysicalShellSource_chart_scale
#print axioms physicalCutoffSource_chart_scale
#print axioms nativeAllScale_physical_cutoff_commutator_assembly
end Yamabe3.Analysis.SpherePolar
