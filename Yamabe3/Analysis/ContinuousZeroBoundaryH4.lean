import Yamabe3.Analysis.BoundaryTangentialH4Estimate
import PoincareLib.Analysis.Sobolev.Boundary.Embedding.Continuous

/-! Local actual zero-boundary Sobolev data force the boundary value of
any continuous representative. This uses continuous zero extension,
not restriction of a volume-a.e. equality to the boundary. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.NirenbergEuclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "H" => halfSpace 3

theorem flat_face_mem_closure_inter {V : Set E} (hV : IsOpen V)
    {x : E} (hx : x ∈ V) (hface : x 0 = 0) : x ∈ closure (V ∩ H) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hV x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t : ℝ := min ε δ / 2
  have ht : 0 < t := div_pos (lt_min hε hδ) (by norm_num)
  have htε : t < ε := (div_lt_self (lt_min hε hδ) (by norm_num)).trans_le (min_le_left _ _)
  have htδ : t < δ := (div_lt_self (lt_min hε hδ) (by norm_num)).trans_le (min_le_right _ _)
  let y : E := x + t • EuclideanSpace.single (0 : Fin 3) 1
  have hd : dist x y = t := by
    dsimp only [y]
    rw [dist_self_add_right, norm_smul]
    simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs,abs_of_pos ht]
  refine ⟨y,⟨hball ?_,?_⟩,hd ▸ htε⟩
  · simpa only [mem_ball,dist_comm,hd] using htδ
  · change (x + t • EuclideanSpace.single (0 : Fin 3) 1 : E) 0 > 0
    simpa [hface] using ht

theorem continuous_boundary_zero_of_memW01p_local_H4
    {u F : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu0 : MemW01p 2 u H) (hu4 : MemWkp 4 2 u (U ∩ H))
    (hF : ContinuousOn F U) (hFu : F =ᵐ[volume.restrict (U ∩ H)] u)
    {x : E} (hx : x ∈ U) (hface : x 0 = 0) : F x = 0 := by
  obtain ⟨V,hV,hxV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := x)) hU (singleton_subset_iff.mpr hx)
  obtain ⟨ψ,hψ,hψc,-,hone,hs⟩ := SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  have hv0 := memW01p_mul_smooth isOpen_halfSpace hu0 hψ hψc
  have hv4 := memWkp_mul_smooth_of_tsupport_subset 4 isOpen_halfSpace hU hu4 hψ hψc hs
  obtain ⟨G,hG,hGae,hGzero⟩ := Poincare.Analysis.Sobolev.BoundaryEmbedding.exists_continuous_zero_extension
    hψc.mul_right hv0 hv4
  have hVsub : V ⊆ U := subset_closure.trans hVU
  have heq : EqOn F G (V ∩ H) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ (hV.inter isOpen_halfSpace)
      (hF.mono (inter_subset_left.trans hVsub)) hG.continuousOn
    filter_upwards [ae_restrict_of_ae hGae,
      ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left H hVsub) hFu,
      ae_restrict_mem (hV.inter isOpen_halfSpace).measurableSet] with y hg hf hy
    change (H).indicator (fun z => ψ z * u z) y = G y at hg
    rw [indicator_of_mem hy.2,hone y (subset_closure hy.1),one_mul] at hg
    exact hf.trans hg
  have hxV' : x ∈ V := hxV (mem_singleton x)
  have hcl := flat_face_mem_closure_inter hV hxV' hface
  have hT : (V ∩ H) ∪ {x} ⊆ U := union_subset (inter_subset_left.trans hVsub) (singleton_subset_iff.mpr hx)
  have hFG : F x = G x := heq.of_subset_closure (hF.mono hT) hG.continuousOn
    subset_union_left (union_subset subset_closure (singleton_subset_iff.mpr hcl)) (Or.inr (mem_singleton x))
  exact hFG.trans (hGzero x hface.le)

#print axioms flat_face_mem_closure_inter
#print axioms continuous_boundary_zero_of_memW01p_local_H4
end Yamabe3.Analysis.UniformElliptic
