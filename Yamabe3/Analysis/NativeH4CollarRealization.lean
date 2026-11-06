import Yamabe3.Analysis.NativeC2CollarEnergyBound
import Yamabe3.Analysis.NativeCollarJetWeakDerivatives
import Yamabe3.Analysis.WeakH4LocalRepresentative
import Yamabe3.Analysis.NativeSmallCollarPotentialError
import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH4Graph

/-! A genuine H4 function on the fixed basic annulus produces one actual
strong C2-jet closure element on the smaller collar. Its norm is bounded
by the original weak H4 norm using uniqueness of weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated

theorem nativeEntranceCollar_closure_subset_basic : closure nativePoissonEntranceCollar⊆halfEndBasicAnnulus := by
  have he : Real.exp (1/2:ℝ)<2 := by
    have hprod : Real.exp (1/2:ℝ)*Real.exp (1/2:ℝ)=Real.exp 1 := by
      rw [←Real.exp_add];norm_num
    nlinarith [Real.exp_pos (1/2:ℝ),Real.exp_one_lt_three]
  have hl : (1/2:ℝ)<Real.exp (-(1/2:ℝ)) := by
    have hprod : Real.exp (-(1/2:ℝ))*Real.exp (1/2:ℝ)=1 := by
      rw [←Real.exp_add];norm_num
    nlinarith [Real.exp_pos (-(1/2:ℝ))]
  intro x hx
  have h := nativePolarTimeWindow_closure_bounds (1/2) hx
  exact ⟨hl.trans_le h.1,h.2.trans_lt he⟩

theorem nativeCollarJet_norm_le_weak_H2 (J : nativeCollarJetClosure) :
    ‖J‖≤(iteratedWeakSobolevNorm 2 2 J.val.1 nativePoissonEntranceCollar).toReal := by
  let O := nativePoissonEntranceCollar
  have hf := (wkpNorm_lt_top_of_memWkp (nativeCollarJetClosure_memH2 J)).ne
  have hj := nativeCollarJetClosure_chosen_jets J
  apply nativeCollarJet_norm_le_of_components J ENNReal.toReal_nonneg
  · rw [Lp.norm_def]
    exact ENNReal.toReal_mono hf (eLpNorm_le_wkpNorm 2 2 J.val.1 O)
  · intro j
    rw [Lp.norm_def,←eLpNorm_congr_ae (hj.1 j)]
    exact ENNReal.toReal_mono hf ((eLpNorm_le_wkpNorm 1 2 (chosenWeakPartial' 2 j J.val.1 O) O).trans
      (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 J.val.1 O j))
  · intro k j
    rw [Lp.norm_def,←eLpNorm_congr_ae (hj.2 k j)]
    exact ENNReal.toReal_mono hf ((eLpNorm_le_wkpNorm 0 2
      (chosenWeakPartial' 2 k (chosenWeakPartial' 2 j J.val.1 O) O) O).trans
      ((wkpNorm_chosenWeakPartial_le_wkpNorm_succ 0 2 (chosenWeakPartial' 2 j J.val.1 O) O k).trans
        (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 J.val.1 O j)))

theorem exists_nativeCollarJet_of_weak_H4 {u : E→ℝ}
    (hu : MemWkp 4 2 u halfEndBasicAnnulus) :
    ∃J : nativeCollarJetClosure,
      (J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u ∧
      ‖J‖≤(iteratedWeakSobolevNorm 4 2 u halfEndBasicAnnulus).toReal := by
  have hO : IsOpen nativePoissonEntranceCollar := nativePolarTimeWindow_open (1/2)
  have hOV := subset_closure.trans nativeEntranceCollar_closure_subset_basic
  obtain ⟨v,U,hU,hOU,hvc,hv,hvu⟩ := exists_compact_sobolev_extension_near_compact
    (locally_of_memWkp halfEndBasicAnnulus_isOpen hu)
    (nativePolarTimeWindow_precompact (1/2)) nativeEntranceCollar_closure_subset_basic
  obtain ⟨F,φ,hF,hFv,-⟩ := exists_compact_weak_H4_C2_representative hv hvc
  let J := nativeC2CollarJetInclusion ⟨F,hF.contDiffOn⟩
  have he : (J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u := by
    filter_upwards [(nativeC2Collar_memLp hF.contDiffOn).1.coeFn_toLp,
      ae_restrict_of_ae hFv,ae_restrict_mem hO.measurableSet] with x hx hf hxO
    exact hx.trans (hf.trans (hvu (hOU (subset_closure hxO))))
  refine ⟨J,he,?_⟩
  have hn := nativeCollarJet_norm_le_weak_H2 J
  rw [wkpNorm_congr_ae (k := 2) (by norm_num) hO he] at hn
  exact hn.trans (ENNReal.toReal_mono (wkpNorm_lt_top_of_memWkp hu).ne
    ((Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated.wkpNorm_mono_order (by norm_num : 2≤4)).trans (wkpNorm_mono_set (by norm_num) hO hOV hu)))

#print axioms nativeEntranceCollar_closure_subset_basic
#print axioms nativeCollarJet_norm_le_weak_H2
#print axioms exists_nativeCollarJet_of_weak_H4
end Yamabe3.Analysis.SpherePolar
