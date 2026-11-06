import Yamabe3.Analysis.LowL2FutureInverse

/-! Exact identification with the original future integral on continuous
L2 sources, before using density to pass its equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem futureL2Convolution_eq_tail (k : ℝ) (F : ℝ → H) (t : ℝ) :
    futureL2Convolution k F t=banachFutureTail k F t := by
  have he : (fun s => futureL2Kernel k (t-s) • F s)=
      (Ici t).indicator (fun s => Real.exp (k*(t-s)) • F s) := by
    funext s
    by_cases hs : t ≤ s
    · have hm : t-s∈Iic (0:ℝ) := sub_nonpos.mpr hs
      simp only [futureL2Kernel,indicator_of_mem hm,indicator_of_mem (show s∈Ici t from hs)]
    · have hm : t-s∉Iic (0:ℝ) := by simpa only [mem_Iic,sub_nonpos] using hs
      simp only [futureL2Kernel,indicator_of_notMem hm,indicator_of_notMem (show s∉Ici t from hs),zero_smul]
  unfold futureL2Convolution
  rw [he,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
  have hx (s : ℝ) : Real.exp (k*(t-s))=Real.exp (k*t)*Real.exp (-k*s) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [hx,mul_smul]
  exact integral_smul _ _

theorem futureL2Resolvent_agrees_original {k : ℝ} (hk : 0<k)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) :
    (futureL2ResolventCLM k hk (hF.toLp F) : ℝ → H)=ᵐ[volume]banachFutureResolvent k hk F := by
  have h := futureL2Resolvent_coe_ae hk (hF.toLp F)
  rw [futureL2Convolution_congr_ae k hF.coeFn_toLp] at h
  filter_upwards [h] with t ht
  exact ht.trans (futureL2Convolution_eq_tail k F t)

theorem banachFutureResolvent_memLp {k : ℝ} (hk : 0<k)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) : MemLp (banachFutureResolvent k hk F) 2 :=
  (Lp.memLp (futureL2ResolventCLM k hk (hF.toLp F))).ae_eq (futureL2Resolvent_agrees_original hk F hF)

theorem doubleFutureL2_agrees_original {k : ℝ} (hk : 0<k)
    (F : ℝ →ᵇ H) (hF : MemLp F 2) :
    (doubleFutureL2CLM k hk (hF.toLp F) : ℝ → H)=ᵐ[volume]banachDoubleFutureResolvent k hk F := by
  have h := futureL2Resolvent_coe_ae hk (futureL2ResolventCLM k hk (hF.toLp F))
  rw [futureL2Convolution_congr_ae k (futureL2Resolvent_agrees_original hk F hF)] at h
  filter_upwards [h] with t ht
  exact ht.trans (futureL2Convolution_eq_tail k (banachFutureResolvent k hk F) t)

#print axioms futureL2Convolution_eq_tail
#print axioms futureL2Resolvent_agrees_original
#print axioms banachFutureResolvent_memLp
#print axioms doubleFutureL2_agrees_original
end Yamabe3.Analysis.Delaunay
