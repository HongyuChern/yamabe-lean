import Yamabe3.Analysis.NativeLogShellPartition

/-! Countable log-shell integration with disjoint measurable intervals;
no infinite sum is justified by a per-shell bound alone. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar

def nativeLogShellInterval (n : ℕ) : Set ℝ := Ioc ((n:ℝ)/2) (((n:ℝ)+1)/2)

theorem nativeLogShellInterval_union : (⋃ n : ℕ,nativeLogShellInterval n)=Ioi 0 := by
  ext t
  simp only [mem_iUnion,mem_Ioi]
  constructor
  · rintro ⟨n,hn⟩
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith [hn.1]
  · intro ht
    obtain ⟨n,hn,_⟩ := nativeLogShell_partition ht
    exact ⟨n,(nativeLogShell_membership n t).mp hn⟩

theorem nativeLogShellInterval_disjoint : Pairwise (fun i j => Disjoint (nativeLogShellInterval i) (nativeLogShellInterval j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  have ht : 0 < t := by have hn0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i;linarith [hi.1]
  obtain ⟨n,hn,hu⟩ := nativeLogShell_partition ht
  have hi' := hu i ((nativeLogShell_membership i t).mpr hi)
  have hj' := hu j ((nativeLogShell_membership j t).mpr hj)
  exact hij (hi'.trans hj'.symm)

theorem nativeLogShell_integral_translate (f : ℝ → ℝ) (n : ℕ) :
    (∫ t in Ioc (-(1/4:ℝ)) (1/4),f (t+nativeLogShellCenter n))=
      ∫ t in nativeLogShellInterval n,f t := by
  rw [←intervalIntegral.integral_of_le (by norm_num : -(1/4:ℝ)≤1/4),
    intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_of_le (by linarith : -(1/4:ℝ)+nativeLogShellCenter n≤1/4+nativeLogShellCenter n)]
  have ha : -(1/4:ℝ)+nativeLogShellCenter n=(n:ℝ)/2 := by unfold nativeLogShellCenter;ring
  have hb : (1/4:ℝ)+nativeLogShellCenter n=((n:ℝ)+1)/2 := by unfold nativeLogShellCenter;ring
  rw [ha,hb]
  rfl

theorem nativeLogShell_integrals_hasSum (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
    HasSum (fun n : ℕ => ∫ t in Ioc (-(1/4:ℝ)) (1/4),f (t+nativeLogShellCenter n))
      (∫ t in Ioi 0,f t) := by
  have hfi : IntegrableOn f (⋃ n : ℕ,nativeLogShellInterval n) := by
    rw [nativeLogShellInterval_union]
    exact hf
  have hm (n : ℕ) : MeasurableSet (nativeLogShellInterval n) := measurableSet_Ioc
  have h := hasSum_integral_iUnion hm nativeLogShellInterval_disjoint hfi
  rw [nativeLogShellInterval_union] at h
  simpa only [nativeLogShell_integral_translate] using h

#print axioms nativeLogShellInterval_union
#print axioms nativeLogShellInterval_disjoint
#print axioms nativeLogShell_integral_translate
#print axioms nativeLogShell_integrals_hasSum
end Yamabe3.Analysis.SpherePolar
