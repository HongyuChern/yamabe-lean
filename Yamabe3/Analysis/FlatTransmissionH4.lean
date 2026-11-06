import Yamabe3.Analysis.DirectionalPieceH4
import Yamabe3.Analysis.HalfSourceTangentialJets

/-! Actual piecewise H2 data produce H4 on the positive side up to the
flat interface, for the same globally H2 weak solution. The tangential
witnesses are constructed and source traces need not agree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.NirenbergEuclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem flat_transmission_positive_H4
    (B : SmoothEllipticBilinearForm d univ)
    {O V : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    {u f g : E → ℝ} (hu : MemWkp 2 2 u O)
    (hf : MemWkp 2 2 f (halfSpace d)) (hg : MemWkp 2 2 g (halfSpace d))
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,twoSidedHalfSource f g x*φ x) :
    MemWkp 4 2 u (V∩halfSpace d) := by
  have hVH := hV.inter (isOpen_halfSpace (d:=d))
  let r (k : Fin d) := twoSidedHalfSource (chosenWeakPartial' 2 k f (halfSpace d))
    (chosenWeakPartial' 2 k g (halfSpace d))
  have hfirst (k : Fin d) (hk : k≠0) := twoSidedHalfSource_first_tangential hf.memW1p hg.memW1p k hk
  have hfV : MemWkp 2 2 (twoSidedHalfSource f g) (V∩halfSpace d) := by
    apply (MemWkp_congr_ae (by norm_num) hVH (u:=f) (v:=twoSidedHalfSource f g) ?_).mp
      (hf.mono_set (by norm_num) hVH inter_subset_right)
    filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
    exact (twoSidedHalfSource_positive f g hx.2).symm
  apply directional_source_H4_on_piece B hO hOc hV hVc hVO hVH inter_subset_left hu
    ((memLp_twoSidedHalfSource hf.memLp hg.memLp).restrict O) hfV r
    (fun k hk => (hfirst k hk).1.restrict O)
    (fun k hk => (hfirst k hk).2.restrict hO (subset_univ O)) _ heq
  intro k s hk hs
  have hh := twoSidedHalfSource_second_tangential hf hg k s hk hs
  exact ⟨hh.1.restrict O,_,hh.2.2.1.restrict O,hh.2.2.2.restrict hO (subset_univ O)⟩

#print axioms flat_transmission_positive_H4
end Yamabe3.Analysis.UniformElliptic
