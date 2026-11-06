import Yamabe3.Analysis.DirectionalSourcePieceRegularity
import Yamabe3.Analysis.BoundaryNormalH4

/-! Two actual tangential derivatives of the source on the full
neighborhood, together with H2 of that source on one piece, give H4 of
the same solution up to that piece. No full cross-interface H3 is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem directional_source_H4_on_piece
    (B : SmoothEllipticBilinearForm d univ)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    (hW : IsOpen W) (hWV : W⊆V)
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemLp f 2 (volume.restrict O))
    (hfW : MemWkp 2 2 f W) (r : Fin d → E → ℝ)
    (hr : ∀k : Fin d,k≠0 → MemLp (r k) 2 (volume.restrict O))
    (hfr : ∀k : Fin d,k≠0 → HasWeakPartialDeriv k (r k) f O)
    (hrr : ∀k s : Fin d,k≠0 → s≠0 → DirectionalL2 s (r k) O)
    (heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
      (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
        fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) :
    MemWkp 4 2 u W := by
  have hfirst (k : Fin d) (hk : k≠0) : DirectionalL2 k f O := ⟨hf,r k,hr k hk,hfr k hk⟩
  have huW3 := directional_source_H3_on_piece B hO hOc hV hVc hVO hW hWV hu hf hfW.memW1p hfirst heq
  have hWc : IsCompact (closure W) := hVc.of_isClosed_subset isClosed_closure (closure_mono hWV)
  have hWO : W⊆O := hWV.trans (subset_closure.trans hVO)
  obtain ⟨U,hU,hVU,hUO⟩ := hVc.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hVO)
  have hUc : IsCompact (closure U) := hOc.of_isClosed_subset isClosed_closure (hUO.trans subset_closure)
  have hsub : U⊆O := subset_closure.trans hUO
  have hWU : W⊆U := hWV.trans (subset_closure.trans hVU)
  have huU := hu.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hU hsub
  have hfU := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have heqU := localized_principal_restrict_canonical hU hsub hu.memW1p heq
  have hpU (k : Fin d) (hk : k≠0) : MemWkp 2 2 (chosenWeakPartial' 2 k u U) U := by
    have hlocal := directional_weak_source_local_H2 hO hOc B.a B.smooth_a
      (fun x _ => smoothElliptic_matrix_posDef B x) hu hf (hr k hk) k (hfr k hk) heq
    exact (MemWkp_congr_ae (by norm_num) hU
      (chosenWeakPartial'_mono_set_ae (by norm_num) hU hsub hu.memW1p k)).mp
      (memWkp_on_precompact_of_locally hlocal hU hUc hUO)
  have htan (k : Fin d) (hk : k≠0) : MemWkp 3 2 (chosenWeakPartial' 2 k u W) W := by
    let G := differentiatedSource B.a (fun j => chosenWeakPartial' 2 j u U)
      (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u U) U) (r k) k
    have hrU := (hr k hk).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hfrU := (hfr k hk).restrict hU hsub
    have hGe := explicit_directional_source_equation hU hUc B.a B.smooth_a huU hfU hrU k hfrU heqU
    have hGW : MemWkp 1 2 G W :=
      explicit_directional_source_H1_on_piece hW hWc hWU B.a B.smooth_a huU huW3 hfW hrU k hfrU
    have hGdir (s : Fin d) (hs : s≠0) : DirectionalL2 s G U := by
      obtain ⟨hrk,t,ht,hwt⟩ := hrr k s hk hs
      have hrsU : DirectionalL2 s (r k) U :=
        ⟨hrk.mono_measure (Measure.restrict_mono hsub le_rfl),t,
          ht.mono_measure (Measure.restrict_mono hsub le_rfl),hwt.restrict hU hsub⟩
      exact directional_differentiated_source hU hUc B.a B.smooth_a huU k s (hpU s hs) hrsU
    have hp3 := directional_source_H3_on_piece B hU hUc hV hVc hVU hW hWV
      (hpU k hk) hGe.1 hGW.memW1p hGdir hGe.2
    exact (MemWkp_congr_ae (by norm_num) hW
      (chosenWeakPartial'_mono_set_ae (by norm_num) hW hWU huU.memW1p k)).mp hp3
  exact memWkp_four_of_tangential_memWkp_three B hW hWc huW3 hfW htan
    (localized_principal_restrict_canonical hW hWO hu.memW1p heq)

#print axioms directional_source_H4_on_piece
end Yamabe3.Analysis.UniformElliptic
