import Yamabe3.Analysis.FlatTransmissionH4
import Yamabe3.Analysis.WeakNormalScaling

/-! Both sides of the same weak solution have H4 up to the interface.
The negative source is transported by the actual reflection, with its
weak derivatives proved independently of any pointwise source trace. -/
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

theorem twoSidedHalfSource_negative (f g : E → ℝ) {x : E} (hx : x 0<0) :
    twoSidedHalfSource f g x=g (normalScaling (-1) (by norm_num) x) := by
  have hxp : x∉halfSpace d := not_lt.mpr hx.le
  have hxn : scaledReflect 1 (by norm_num) x∈halfSpace d := by
    change 0<scaledReflect 1 (by norm_num) x 0
    rw [scaledReflect_normal]
    linarith
  simp only [twoSidedHalfSource,Pi.add_apply,indicator_of_notMem hxp,zero_add,
    reflectedSample,indicator_of_mem hxn]
  rfl

theorem flat_transmission_both_sides_H4
    (B : SmoothEllipticBilinearForm d univ)
    {O V : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    {u f g : E → ℝ} (hu : MemWkp 2 2 u O)
    (hf : MemWkp 2 2 f (halfSpace d)) (hg : MemWkp 2 2 g (halfSpace d))
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,twoSidedHalfSource f g x*φ x) :
    MemWkp 4 2 u (V∩halfSpace d) ∧ MemWkp 4 2 u (V∩{x : E | x 0<0}) := by
  refine ⟨flat_transmission_positive_H4 B hO hOc hV hVc hVO hu hf hg heq,?_⟩
  let N := normalScaling (d:=d) (-1) (by norm_num)
  have hset : N ⁻¹' halfSpace d={x : E | x 0<0} := by
    ext x
    simp [N,halfSpace,normalFactor]
  have hNeg : IsOpen {x : E | x 0<0} := hset ▸ isOpen_halfSpace.preimage N.continuous
  have hVN := hV.inter hNeg
  have hgN : MemWkp 2 2 (fun x => g (N x)) {x : E | x 0<0} := by
    rw [← hset]
    exact memWkp_comp_normalScaling (by norm_num) isOpen_halfSpace (by norm_num) 2 hg
  have hfV : MemWkp 2 2 (twoSidedHalfSource f g) (V∩{x : E | x 0<0}) := by
    apply (MemWkp_congr_ae (by norm_num) hVN
      (u:=fun x => g (N x)) (v:=twoSidedHalfSource f g) ?_).mp
      (hgN.mono_set (by norm_num) hVN inter_subset_right)
    filter_upwards [ae_restrict_mem hVN.measurableSet] with x hx
    exact (twoSidedHalfSource_negative f g hx.2).symm
  let r (k : Fin d) := twoSidedHalfSource (chosenWeakPartial' 2 k f (halfSpace d))
    (chosenWeakPartial' 2 k g (halfSpace d))
  have hfirst (k : Fin d) (hk : k≠0) := twoSidedHalfSource_first_tangential hf.memW1p hg.memW1p k hk
  apply directional_source_H4_on_piece B hO hOc hV hVc hVO hVN inter_subset_left hu
    ((memLp_twoSidedHalfSource hf.memLp hg.memLp).restrict O) hfV r
    (fun k hk => (hfirst k hk).1.restrict O)
    (fun k hk => (hfirst k hk).2.restrict hO (subset_univ O)) _ heq
  intro k s hk hs
  have hh := twoSidedHalfSource_second_tangential hf hg k s hk hs
  exact ⟨hh.1.restrict O,_,hh.2.2.1.restrict O,hh.2.2.2.restrict hO (subset_univ O)⟩

#print axioms twoSidedHalfSource_negative
#print axioms flat_transmission_both_sides_H4
end Yamabe3.Analysis.UniformElliptic
