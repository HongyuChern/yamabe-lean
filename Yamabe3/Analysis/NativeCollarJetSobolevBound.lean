import Yamabe3.Analysis.NativeH4CollarRealization

/-! The actual Sobolev H2 norm is controlled by the retained finite jet
norm. This is the converse estimate needed for source-independent
transmission bounds; the value and both derivative orders are counted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated

theorem nativeCollarJet_weak_H2_le (J : nativeCollarJetClosure) :
    iteratedWeakSobolevNorm 2 2 J.val.1 nativePoissonEntranceCollar ≤13*ENNReal.ofReal ‖J‖ := by
  let O := nativePoissonEntranceCollar
  let N := ENNReal.ofReal ‖J‖
  have h0 : ‖J.val.1‖≤‖J‖ := by
    change ‖J.val.1‖≤‖J.val‖
    rw [Prod.norm_def]
    exact le_max_left _ _
  have h1 (j : Fin 3) : ‖J.val.2.1 j‖≤‖J‖ := by
    have h := norm_le_pi_norm J.val.2.1 j
    apply h.trans
    change ‖J.val.2.1‖≤‖J.val‖
    rw [Prod.norm_def,Prod.norm_def]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have h2 (i j : Fin 3) : ‖J.val.2.2 i j‖≤‖J‖ := by
    apply (norm_le_pi_norm (J.val.2.2 i) j).trans
    apply (norm_le_pi_norm J.val.2.2 i).trans
    change ‖J.val.2.2‖≤‖J.val‖
    rw [Prod.norm_def,Prod.norm_def]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have he0 : eLpNorm (J.val.1 : E → ℝ) 2 (volume.restrict O)≤N := by
    rw [←Lp.enorm_def,←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h0
  have hj := nativeCollarJetClosure_chosen_jets J
  have he1 (j : Fin 3) : eLpNorm (chosenWeakPartial' 2 j J.val.1 O) 2 (volume.restrict O)≤N := by
    rw [eLpNorm_congr_ae (hj.1 j),←Lp.enorm_def,←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h1 j)
  have he2 (i j : Fin 3) : eLpNorm (chosenWeakPartial' 2 i (chosenWeakPartial' 2 j J.val.1 O) O) 2 (volume.restrict O)≤N := by
    rw [eLpNorm_congr_ae (hj.2 i j),←Lp.enorm_def,←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h2 i j)
  change iteratedWeakSobolevNorm 2 2 J.val.1 O≤13*N
  rw [wkpNorm_succ_eq 1]
  calc
    _ ≤ N+∑j : Fin 3,(N+∑i : Fin 3,N) := by
      apply add_le_add he0
      apply Finset.sum_le_sum
      intro j _
      rw [wkpNorm_succ_eq 0]
      exact add_le_add (he1 j) (Finset.sum_le_sum (fun i _ => by simpa only [wkpNorm_zero] using he2 i j))
    _ = _ := by simp only [Fin.sum_univ_three];ring

#print axioms nativeCollarJet_weak_H2_le
end Yamabe3.Analysis.SpherePolar
