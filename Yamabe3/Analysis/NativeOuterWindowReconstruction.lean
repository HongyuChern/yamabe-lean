import Yamabe3.Analysis.NativeFiniteOuterWindowSource
import Yamabe3.Analysis.NativeFullSourceReconstruction

/-! Exact finite exterior-window reconstruction on ALL angular modes.
The disjoint half-open endpoints and actual time translations are kept;
finite window membership is not inferred just from a shell norm estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay

def nativeOuterLogShellInterval (n:ℕ):Set ℝ := Ioc (-((n:ℝ)+1)/2) (-(n:ℝ)/2)

theorem nativeOuterLogWindow_union (m:ℕ):
    (⋃i:Fin m,nativeOuterLogShellInterval i)=Ioc (-(m:ℝ)/2) 0 := by
  ext t
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i,hi⟩
    have hi':(i.val:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
    have hi0:(0:ℝ) ≤ i.val := Nat.cast_nonneg _
    exact ⟨by linarith [hi.1],by linarith [hi.2]⟩
  · intro ht
    obtain ⟨i,hi,_⟩:=nativeOuterLogWindow_partition m ht
    exact ⟨i,(nativeOuterLogShell_membership i t).mp hi⟩

theorem nativeOuterLogWindow_disjoint (m:ℕ):
    Pairwise (fun i j:Fin m=>Disjoint (nativeOuterLogShellInterval i) (nativeOuterLogShellInterval j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  have ht:t∈Ioc (-(m:ℝ)/2) 0 := by
    rw [←nativeOuterLogWindow_union]
    exact mem_iUnion.mpr ⟨i,hi⟩
  obtain ⟨n,hn,hu⟩:=nativeOuterLogWindow_partition m ht
  have hi':=hu i ((nativeOuterLogShell_membership i t).mpr hi)
  have hj':=hu j ((nativeOuterLogShell_membership j t).mpr hj)
  exact hij (hi'.trans hj'.symm)

theorem nativeOuterLogShell_integral_translate (f:ℝ→ℝ) (n:ℕ):
    (∫t in Ioc (-(1/4:ℝ)) (1/4),f (t+nativeOuterLogShellCenter n))=
      ∫t in nativeOuterLogShellInterval n,f t := by
  rw [←intervalIntegral.integral_of_le (by norm_num:-(1/4:ℝ) ≤ 1/4),
    intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_of_le (by linarith:-(1/4:ℝ)+nativeOuterLogShellCenter n ≤ 1/4+nativeOuterLogShellCenter n)]
  have ha:-(1/4:ℝ)+nativeOuterLogShellCenter n= -((n:ℝ)+1)/2 := by unfold nativeOuterLogShellCenter;ring
  have hb:(1/4:ℝ)+nativeOuterLogShellCenter n= -(n:ℝ)/2 := by unfold nativeOuterLogShellCenter;ring
  rw [ha,hb]
  rfl

theorem nativeOuterLogWindow_integrals (m:ℕ) (f:ℝ→ℝ)
    (hf:IntegrableOn f (Ioc (-(m:ℝ)/2) 0)) :
    (∑i:Fin m,∫t in Ioc (-(1/4:ℝ)) (1/4),f (t+nativeOuterLogShellCenter i))=
      ∫t in Ioc (-(m:ℝ)/2) 0,f t := by
  have hfi:IntegrableOn f (⋃i:Fin m,nativeOuterLogShellInterval i) := by
    rw [nativeOuterLogWindow_union]
    exact hf
  have hh:=hasSum_integral_iUnion (fun i:Fin m=>show MeasurableSet (nativeOuterLogShellInterval i) from measurableSet_Ioc)
    (nativeOuterLogWindow_disjoint m) hfi
  rw [nativeOuterLogWindow_union] at hh
  simpa only [nativeOuterLogShell_integral_translate,tsum_fintype] using hh.tsum_eq

theorem nativeFiniteOuterWindowSource_reconstructs (m:ℕ)
    (F G:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) :
    inner ℝ
      (nativeFiniteOuterWindowSourceCLM m (fun i=>nativeL2FullPhysicalSourceCLM.comp
        (l2TimeTranslateCLM AngularSpectralSpace (nativeOuterLogShellCenter i))) F) G=
      ∫t in Ioc (-(m:ℝ)/2) 0,inner ℝ (F t) (G t) := by
  simp only [nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,sum_inner,
    nativeFullShellSourceReturn_source_pairing]
  exact nativeOuterLogWindow_integrals m _ (L2.integrable_inner (𝕜:=ℝ) F G).integrableOn

#print axioms nativeOuterLogWindow_union
#print axioms nativeOuterLogWindow_disjoint
#print axioms nativeOuterLogWindow_integrals
#print axioms nativeFiniteOuterWindowSource_reconstructs
end Yamabe3.Analysis.SpherePolar
