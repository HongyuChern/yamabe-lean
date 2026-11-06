import Yamabe3.Analysis.NativeShellSourceReturn
import Mathlib.Analysis.SpecificLimits.Normed

/-! Disjoint half-open logarithmic shells cover every positive time.
The actual geometric decay pays the infinite-shell summation cost. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

def nativeLogShellCenter (n : ℕ) : ℝ := (n:ℝ)/2+1/4

theorem nativeLogShellCenter_nonneg (n : ℕ) : 0 ≤ nativeLogShellCenter n := by
  unfold nativeLogShellCenter
  positivity

theorem nativeLogShell_membership (n : ℕ) (t : ℝ) :
    t-nativeLogShellCenter n ∈ Ioc (-(1/4:ℝ)) (1/4) ↔
      t∈Ioc ((n:ℝ)/2) (((n:ℝ)+1)/2) := by
  simp only [mem_Ioc,nativeLogShellCenter]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem nativeLogShell_partition {t : ℝ} (ht : 0<t) :
    ∃! n : ℕ,t-nativeLogShellCenter n ∈ Ioc (-(1/4:ℝ)) (1/4) := by
  let m := Nat.ceil (2*t)
  have hm : 0 < m := Nat.ceil_pos.mpr (by positivity)
  let n := m-1
  have hn : n < m := Nat.sub_lt hm (by decide : 0<1)
  have hl : (n:ℝ)<2*t := Nat.lt_ceil.mp hn
  have hu : 2*t≤(m:ℝ) := Nat.le_ceil _
  have he : (n:ℝ)+1=(m:ℝ) := by exact_mod_cast Nat.sub_add_cancel hm
  refine ⟨n,(nativeLogShell_membership n t).mpr ⟨by linarith,by linarith⟩,?_⟩
  intro k hk
  have hk' := (nativeLogShell_membership k t).mp hk
  apply le_antisymm
  · by_contra h
    have hkn : n+1≤k := by omega
    have hkn' : (n:ℝ)+1≤(k:ℝ) := by exact_mod_cast hkn
    linarith [hk'.1]
  · by_contra h
    have hkn : k+1≤n := by omega
    have hkn' : (k:ℝ)+1≤(n:ℝ) := by exact_mod_cast hkn
    linarith [hk'.2]

theorem nativeLogShell_decay (n : ℕ) :
    Real.exp (-nativeLogShellCenter n)=
      Real.exp (-(1/4:ℝ))*Real.exp (-(1/2:ℝ))^n := by
  rw [nativeLogShellCenter]
  have he : -((n:ℝ)/2+1/4)=-(1/4:ℝ)+(n:ℝ)*(-(1/2:ℝ)) := by ring
  rw [he,Real.exp_add,Real.exp_nat_mul]

theorem nativeLogShell_decay_summable :
    Summable (fun n : ℕ => Real.exp (-nativeLogShellCenter n)) := by
  simp_rw [nativeLogShell_decay]
  exact (summable_geometric_of_lt_one (Real.exp_pos (-(1/2:ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _

theorem nativeLogShell_decay_sum :
    (∑' n : ℕ,Real.exp (-nativeLogShellCenter n))=
      Real.exp (-(1/4:ℝ))*(1-Real.exp (-(1/2:ℝ)))⁻¹ := by
  simp_rw [nativeLogShell_decay]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.exp_pos (-(1/2:ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num))]

#print axioms nativeLogShell_partition
#print axioms nativeLogShell_decay_summable
#print axioms nativeLogShell_decay_sum
end Yamabe3.Analysis.SpherePolar
