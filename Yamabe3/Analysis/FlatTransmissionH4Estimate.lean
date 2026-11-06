import Yamabe3.Analysis.DirectionalPieceH4Estimate
import Yamabe3.Analysis.HalfSourceTangentialBounds

/-! Actual one-sided H4 transmission estimate in three dimensions.
Both source pieces are original H2 inputs; their traces may jump. All
tangential derivative witnesses and their bounds are produced internally. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean Poincare.Analysis.Sobolev.BoundaryTangential
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_flat_transmission_positive_H4_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {O V : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ u f g : E → ℝ,
      MemWkp 2 2 u O → MemWkp 2 2 f (halfSpace 3) → MemWkp 2 2 g (halfSpace 3) →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,twoSidedHalfSource f g x*φ x) →
      MemWkp 4 2 u (V∩halfSpace 3) ∧
      iteratedWeakSobolevNorm 4 2 u (V∩halfSpace 3) ≤ C *
        (iteratedWeakSobolevNorm 2 2 u O+
          (iteratedWeakSobolevNorm 2 2 f (halfSpace 3)+iteratedWeakSobolevNorm 2 2 g (halfSpace 3))) := by
  let W := V∩halfSpace 3
  have hW : IsOpen W := hV.inter isOpen_halfSpace
  obtain ⟨C,hC,hb⟩ := exists_directional_piece_H4_bound B hO hOc hV hVc hVO hW inter_subset_left
  refine ⟨C,hC,?_⟩
  intro u f g hu hf hg heq
  let N := iteratedWeakSobolevNorm 2 2 u O+
    (iteratedWeakSobolevNorm 2 2 f (halfSpace 3)+iteratedWeakSobolevNorm 2 2 g (halfSpace 3))
  let R := twoSidedHalfSource f g
  let r := fun k : Fin 3 => twoSidedHalfSource (chosenWeakPartial' 2 k f (halfSpace 3))
    (chosenWeakPartial' 2 k g (halfSpace 3))
  let t := fun k s : Fin 3 => twoSidedHalfSource
    (chosenWeakPartial' 2 s (chosenWeakPartial' 2 k f (halfSpace 3)) (halfSpace 3))
    (chosenWeakPartial' 2 s (chosenWeakPartial' 2 k g (halfSpace 3)) (halfSpace 3))
  have hR : MemLp R 2 (volume.restrict O) := (memLp_twoSidedHalfSource hf.memLp hg.memLp).restrict O
  have heR : R =ᵐ[volume.restrict W] f := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    exact twoSidedHalfSource_positive f g hx.2
  have hRW : MemWkp 2 2 R W := (MemWkp_congr_ae (by norm_num) hW heR.symm).mp
    (hf.mono_set (by norm_num) hW inter_subset_right)
  have hfirst (k : Fin 3) (hk : k≠0) := twoSidedHalfSource_first_tangential hf.memW1p hg.memW1p k hk
  have hsecond (k s : Fin 3) (hk : k≠0) (hs : s≠0) := twoSidedHalfSource_second_tangential hf hg k s hk hs
  have hRN : iteratedWeakSobolevNorm 2 2 R W≤N := by
    rw [wkpNorm_congr_ae (k:=2) (by norm_num : (1:ℝ≥0∞)≤2) hW heR]
    exact (wkpNorm_mono_set (by norm_num) hW inter_subset_right hf).trans
      ((le_add_right le_rfl).trans (le_add_left le_rfl))
  have hrN (k : Fin 3) : iteratedWeakSobolevNorm 0 2 (r k) O≤N :=
    (twoSidedHalfSource_first_norm_le hf.le_succ hg.le_succ k O).trans
      ((add_le_add (wkpNorm_mono_order (by norm_num : 1≤2) f (halfSpace 3))
        (wkpNorm_mono_order (by norm_num : 1≤2) g (halfSpace 3))).trans (le_add_left le_rfl))
  have htN (k s : Fin 3) : iteratedWeakSobolevNorm 0 2 (t k s) O≤N :=
    (twoSidedHalfSource_second_norm_le hf hg k s O).trans (le_add_left le_rfl)
  exact hb N u R r t hu hR hRW
    (fun k hk => (hfirst k hk).1.restrict O)
    (fun k hk => (hfirst k hk).2.restrict hO (subset_univ _))
    (fun k s hk hs => (hsecond k s hk hs).2.2.1.restrict O)
    (fun k s hk hs => (hsecond k s hk hs).2.2.2.restrict hO (subset_univ _))
    (le_add_right le_rfl) hRN (fun k _ => hrN k) (fun k s _ _ => htN k s) heq

#print axioms exists_flat_transmission_positive_H4_estimate
end Yamabe3.Analysis.UniformElliptic
