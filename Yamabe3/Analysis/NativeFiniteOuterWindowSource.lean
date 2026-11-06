import Yamabe3.Analysis.NativeLogShellPartition
import Yamabe3.Analysis.NativePhysicalPairTestScaling
import Yamabe3.Analysis.NativeFullShellReturn

/-! A finite exterior logarithmic window has disjoint actual shell
returns. The full finite sum cost and physical testing factors are
retained. This source assembler does not itself assert geometric PDE
cancellation: the actual exterior rows must be constructed separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay

def nativeOuterLogShellCenter (n:ℕ):ℝ := -(n:ℝ)/2-1/4

theorem nativeOuterLogShell_membership (n:ℕ) (t:ℝ) :
    t-nativeOuterLogShellCenter n∈Ioc (-(1/4:ℝ)) (1/4) ↔
      t∈Ioc (-((n:ℝ)+1)/2) (-(n:ℝ)/2) := by
  simp only [nativeOuterLogShellCenter,mem_Ioc]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem nativeOuterLogWindow_partition (m:ℕ) {t:ℝ}
    (ht:t∈Ioc (-(m:ℝ)/2) 0) :
    ∃!n:Fin m,t-nativeOuterLogShellCenter n∈Ioc (-(1/4:ℝ)) (1/4) := by
  let n:=⌊-2*t⌋₊
  have hn:(n:ℝ)≤-2*t := Nat.floor_le (by linarith [ht.2])
  have hn':-2*t<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hnm : n < m := by
    by_contra h
    have hm:m≤n := Nat.le_of_not_gt h
    have hm':(m:ℝ)≤(n:ℝ) := by exact_mod_cast hm
    linarith [ht.1]
  refine ⟨⟨n,hnm⟩,(nativeOuterLogShell_membership n t).mpr ⟨by linarith,by linarith⟩,?_⟩
  intro k hk
  have hh: t∈Ioc (-((k.val:ℝ)+1)/2) (-(k.val:ℝ)/2) := (nativeOuterLogShell_membership k t).mp hk
  apply Fin.ext
  change k.val=n
  apply le_antisymm
  · by_contra h
    have hkn:n+1≤k.val := by omega
    have hkn':(n:ℝ)+1≤(k.val:ℝ) := by exact_mod_cast hkn
    linarith [hh.2]
  · by_contra h
    have hkn:k.val+1≤n := by omega
    have hkn':(k.val:ℝ)+1≤(n:ℝ) := by exact_mod_cast hkn
    linarith [hh.1]

variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def nativeFiniteOuterWindowSourceCLM (m:ℕ) (rows:Fin m→X →L[ℝ] NativeCollarL2) :
    X →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ) :=
  ∑i:Fin m,(nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)).comp (rows i)

theorem nativeFiniteOuterWindowSource_norm (m:ℕ) (rows:Fin m→X →L[ℝ] NativeCollarL2) :
    ‖nativeFiniteOuterWindowSourceCLM m rows‖≤
      (‖nativeL2FullPhysicalSourceCLM‖*Real.exp 1)*∑i:Fin m,‖rows i‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (nativeFullShellSourceReturn_norm _) (norm_nonneg _))

theorem nativeFiniteOuterWindowSource_physical_test (m:ℕ) (rows:Fin m→X →L[ℝ] NativeCollarL2)
    (x:X) (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    inner ℝ (nativeFiniteOuterWindowSourceCLM m rows x) (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∑i:Fin m,Real.exp (-5*nativeOuterLogShellCenter i/2)*
        (∫y in nativeSourceShell,rows i x y*φ (Real.exp (-nativeOuterLogShellCenter i) • y)) := by
  simp only [nativeFiniteOuterWindowSourceCLM,ContinuousLinearMap.sum_apply,sum_inner,
    ContinuousLinearMap.comp_apply,nativeFullShellSourceReturn_physical_test]

#print axioms nativeOuterLogWindow_partition
#print axioms nativeFiniteOuterWindowSource_norm
#print axioms nativeFiniteOuterWindowSource_physical_test
end Yamabe3.Analysis.SpherePolar
