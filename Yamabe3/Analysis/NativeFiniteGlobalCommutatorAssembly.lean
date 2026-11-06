import Yamabe3.Analysis.NativeGlobalPhysicalCutoffSource

/-! Exact finite physical commutator assembly. Genuine derivative
support and the disjoint half-open physical shell partition identify
the entire finite sum with ONE fixed-scale physical cutoff source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration

 theorem nativeScaledSourceShell_subset_outerWindow
    {S:ℝ} {N:ℕ} (hS:S≤-(1/4:ℝ)) (hN:-S+1/4≤(N:ℝ)/2):
    nativeScaledSourceShell S⊆nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0):=by
  intro x hx
  obtain ⟨hx0,hl,hr⟩:=(nativeScaledSourceShell_mem S x).mp hx
  exact ⟨hx0,by linarith,by linarith⟩

 theorem nativeFiniteGlobal_cutoff_commutator_assembly
    {u:E→ℝ} (hu:MemWkp 1 2 u univ) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (S:ℝ) (N:ℕ) (hS:S≤-(1/4:ℝ)) (hN:-S+1/4≤(N:ℝ)/2)
    (J:Fin N→nativeCollarJetClosure)
    (hJ:∀i:Fin N,(J i).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weightedPhysicalDilation (nativeOuterLogShellCenter i) u):
    (fun x:E=>∑i:Fin N,nativePhysicalShellSource 1 (nativeOuterLogShellCenter i)
      (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J i).val) x)=ᵐ[volume]
      physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation S u) S 1:=by
  classical
  let f:E→ℝ:=weakCutoffCommutator univ (fun x=>χ (Real.exp S • x)) u
  have hrow(i:Fin N):=nativeCutoffJet_global_shell_source hu χ hχ S (nativeOuterLogShellCenter i) (J i) (hJ i)
  have hphys:=nativePhysicalCutoffSource_global_commutator hu χ S hs
  filter_upwards [eventually_all.mpr hrow,hphys] with x hx hp
  rw [hp]
  change (∑i:Fin N,_)=8*f x
  simp_rw [hx]
  change (∑i:Fin N,8*(nativeScaledSourceShell (nativeOuterLogShellCenter i)).indicator f x)=8*f x
  by_cases hxW:x∈nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0)
  · have hxU:x∈⋃i:Fin N,nativeScaledSourceShell (nativeOuterLogShellCenter i):=by
      rw [nativeScaledOuterWindow_union]
      exact hxW
    obtain ⟨i,hi⟩:=mem_iUnion.mp hxU
    rw [Finset.sum_eq_single i]
    · rw [indicator_of_mem hi]
    · intro j _ hji
      have hj:x∉nativeScaledSourceShell (nativeOuterLogShellCenter j):=by
        intro hxj
        exact disjoint_left.mp (nativeScaledOuterShell_disjoint N hji) hxj hi
      rw [indicator_of_notMem hj,mul_zero]
    · simp
  · have hxs:x∉nativeScaledSourceShell S:=fun hxS=>hxW (nativeScaledSourceShell_subset_outerWindow hS hN hxS)
    have hf:f x=0:=nativeScaledCutoffCommutator_zero_off_shell χ u S hs hxs
    have hz(i:Fin N):(nativeScaledSourceShell (nativeOuterLogShellCenter i)).indicator f x=0:=by
      by_cases hi:x∈nativeScaledSourceShell (nativeOuterLogShellCenter i)
      · rw [indicator_of_mem hi,hf]
      · rw [indicator_of_notMem hi]
    simp only [hz,mul_zero,Finset.sum_const_zero,hf]

#print axioms nativeScaledSourceShell_subset_outerWindow
#print axioms nativeFiniteGlobal_cutoff_commutator_assembly
end Yamabe3.Analysis.SpherePolar
