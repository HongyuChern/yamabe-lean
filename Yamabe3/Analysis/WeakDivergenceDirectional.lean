import Yamabe3.Analysis.DirectionalCommutatorBound

/-! Differentiate the actual weak divergence operator in one direction.
Only H2 of that chosen directional derivative is used, not full H3 of u. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakPartial_add_memLp {O : Set E} {k : Fin d} {f g r s : E → ℝ}
    (hf : MemLp f 2 (volume.restrict O)) (hg : MemLp g 2 (volume.restrict O))
    (hr : MemLp r 2 (volume.restrict O)) (hs : MemLp s 2 (volume.restrict O))
    (hfr : HasWeakPartialDeriv k r f O) (hgs : HasWeakPartialDeriv k s g O) :
    HasWeakPartialDeriv k (fun x => r x+s x) (fun x => f x+g x) O := by
  intro φ hφ hc ht
  have hφL : MemLp φ 2 (volume.restrict O) := (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDL : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) 2 (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  have ha := integral_add (hf.integrable_mul hDL) (hg.integrable_mul hDL)
  have hb := integral_add (hr.integrable_mul hφL) (hs.integrable_mul hφL)
  simp only [Pi.mul_apply] at ha hb
  simp only [add_mul]
  rw [ha,hb,hfr φ hφ hc ht,hgs φ hφ hc ht]
  ring

theorem weakPartial_neg_exact {O : Set E} {k : Fin d} {f r : E → ℝ}
    (hfr : HasWeakPartialDeriv k r f O) :
    HasWeakPartialDeriv k (fun x => -r x) (fun x => -f x) O := by
  intro φ hφ hc ht
  simp only [neg_mul,integral_neg]
  rw [hfr φ hφ hc ht]

theorem weakPartial_weakDivergenceSource {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j)) {u : E → ℝ}
    (hu : MemWkp 2 2 u O) (s : Fin d)
    (hv : MemWkp 2 2 (chosenWeakPartial' 2 s u O) O) :
    HasWeakPartialDeriv s
      (fun x => weakDivergenceSource O a (chosenWeakPartial' 2 s u O) x+
        weakDivergenceSource O (fun x i j => partialDeriv s (fun y => a y i j) x) u x)
      (weakDivergenceSource O a u) O := by
  let v := chosenWeakPartial' 2 s u O
  let p := fun j => chosenWeakPartial' 2 j u O
  let q := fun i j => chosenWeakPartial' 2 i (p j) O
  let pv := fun j => chosenWeakPartial' 2 j v O
  let qv := fun i j => chosenWeakPartial' 2 i (pv j) O
  have hp (j : Fin d) : MemWkp 1 2 (p j) O := hu.chosenWeakPartial_mem j
  have hq (i j : Fin d) : MemLp (q i j) 2 (volume.restrict O) := (hp j).chosenWeakPartial_mem i
  have hpv (j : Fin d) : MemWkp 1 2 (pv j) O := hv.chosenWeakPartial_mem j
  have hqv (i j : Fin d) : MemLp (qv i j) 2 (volume.restrict O) := (hpv j).chosenWeakPartial_mem i
  have hwp (j : Fin d) : HasWeakPartialDeriv s (pv j) (p j) O :=
    weakPartial_commute s j (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p s)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartial'_isWeakPartial_of_mem hv.memW1p j)
  have hwq (i j : Fin d) : HasWeakPartialDeriv s (qv i j) (q i j) O :=
    weakPartial_commute s i (hwp j) (chosenWeakPartial'_isWeakPartial_of_mem (hp j).memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem (hpv j).memW1p i)
  let G := fun i j x => a x i j*q i j x+partialDeriv i (fun y => a y i j) x*p j x
  let T := fun i j x =>
    (a x i j*qv i j x+partialDeriv s (fun y => a y i j) x*q i j x)+
    (partialDeriv i (fun y => a y i j) x*pv j x+
      partialDeriv s (partialDeriv i (fun y => a y i j)) x*p j x)
  have hm {b w : E → ℝ} (hb : ContDiff ℝ ∞ b) (hw : MemLp w 2 (volume.restrict O)) :
      MemLp (fun x => b x*w x) 2 (volume.restrict O) :=
    memWkp_mul_smooth_of_isCompact_closure 0 hO hOc hw hb
  have hG (i j : Fin d) : MemLp (G i j) 2 (volume.restrict O) :=
    (hm (ha i j) (hq i j)).add (hm (contDiff_partial (ha i j) i) (hp j).memLp)
  have hT (i j : Fin d) : MemLp (T i j) 2 (volume.restrict O) :=
    ((hm (ha i j) (hqv i j)).add (hm (contDiff_partial (ha i j) s) (hq i j))).add
      ((hm (contDiff_partial (ha i j) i) (hpv j).memLp).add
        (hm (contDiff_partial (contDiff_partial (ha i j) i) s) (hp j).memLp))
  have hw (i j : Fin d) : HasWeakPartialDeriv s (T i j) (G i j) O :=
    weakPartial_add_memLp (hm (ha i j) (hq i j)) (hm (contDiff_partial (ha i j) i) (hp j).memLp)
      ((hm (ha i j) (hqv i j)).add (hm (contDiff_partial (ha i j) s) (hq i j)))
      ((hm (contDiff_partial (ha i j) i) (hpv j).memLp).add
        (hm (contDiff_partial (contDiff_partial (ha i j) i) s) (hp j).memLp))
      ((hwq i j).mul_smooth hO (ha i j) ((hq i j).locallyIntegrable (by norm_num))
        ((hqv i j).locallyIntegrable (by norm_num)))
      ((hwp j).mul_smooth hO (contDiff_partial (ha i j) i) ((hp j).memLp.locallyIntegrable (by norm_num))
        ((hpv j).memLp.locallyIntegrable (by norm_num)))
  have hh : HasWeakPartialDeriv s (fun x => ∑ i,∑ j,T i j x) (fun x => ∑ i,∑ j,G i j x) O :=
    weakPartial_finset_sum Finset.univ
      (fun i _ => (memLp_finsetSum _ (fun j _ => hG i j)).locallyIntegrable (by norm_num))
      (fun i _ => (memLp_finsetSum _ (fun j _ => hT i j)).locallyIntegrable (by norm_num))
      (fun i _ => weakPartial_finset_sum Finset.univ
        (fun j _ => (hG i j).locallyIntegrable (by norm_num))
        (fun j _ => (hT i j).locallyIntegrable (by norm_num)) (fun j _ => hw i j))
  have ht : (fun x => -(∑ i,∑ j,T i j x)) =
      fun x => weakDivergenceSource O a v x+
        weakDivergenceSource O (fun x i j => partialDeriv s (fun y => a y i j) x) u x := by
    funext x
    dsimp only [T,weakDivergenceSource,pv,qv,p,q]
    simp_rw [partial_comm (ha _ _) s]
    have hterm (i j : Fin d) :
        (a x i j*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j v O) O x+
          partialDeriv s (fun y => a y i j) x*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x)+
        (partialDeriv i (fun y => a y i j) x*chosenWeakPartial' 2 j v O x+
          partialDeriv i (partialDeriv s (fun y => a y i j)) x*chosenWeakPartial' 2 j u O x)=
        (a x i j*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j v O) O x+
          partialDeriv i (fun y => a y i j) x*chosenWeakPartial' 2 j v O x)+
        (partialDeriv s (fun y => a y i j) x*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x+
          partialDeriv i (partialDeriv s (fun y => a y i j)) x*chosenWeakPartial' 2 j u O x) := by ring
    simp_rw [hterm,Finset.sum_add_distrib]
    ring
  have hn := weakPartial_neg_exact hh
  rw [ht] at hn
  exact hn

#print axioms weakPartial_add_memLp
#print axioms weakPartial_neg_exact
#print axioms weakPartial_weakDivergenceSource
end Yamabe3.Analysis.UniformElliptic
