import Yamabe3.Analysis.BoundaryH2SobolevEstimate
import Yamabe3.Analysis.BoundaryLocalizedSourceBound
import Yamabe3.Analysis.BoundaryQuantitativeInterfaces

/-! Tangential H3 estimates are produced from the true zero-boundary
solution by cutoff localization and the differentiated original equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_flat_tangential_H3_estimate
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) (l : Fin d) (hl : l ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemW01p 2 u (halfSpace d) → MemWkp 2 2 u (halfSpace d) → MemWkp 1 2 f (halfSpace d) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ halfSpace d →
        (∫ x in halfSpace d, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in halfSpace d, f x * φ x) →
      MemWkp 2 2 (chosenWeakPartial' 2 l u (V ∩ halfSpace d)) (V ∩ halfSpace d) ∧
      iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 l u (V ∩ halfSpace d)) (V ∩ halfSpace d) ≤
        K * (iteratedWeakSobolevNorm 2 2 u (halfSpace d) + iteratedWeakSobolevNorm 1 2 f (halfSpace d)) := by
  classical
  let H : Set E := halfSpace d
  obtain ⟨U, hU, hVU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  have hUH : IsOpen (U ∩ H) := hU.inter isOpen_halfSpace
  have hVH : IsOpen (V ∩ H) := hV.inter isOpen_halfSpace
  have hUHc : IsCompact (closure (U ∩ H)) := hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ := SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  obtain ⟨Cd, hCd, hdiff⟩ := exists_differentiated_source_uniform_bound 0 hUH hUHc B.a B.smooth_a l
  obtain ⟨Cl, hCl, hloc⟩ := exists_localized_source_uniform_bound 0 isOpen_halfSpace hU B.a B.smooth_a χ hχ hc hs
  obtain ⟨Cm, hCm, hmul⟩ := exists_localized_sobolev_multiplier_bound 1 isOpen_halfSpace hU χ hχ hc hs
  obtain ⟨C2, hC2, htwo⟩ := exists_flat_H2_sobolev_estimate B hU hUc hV hVc hVU
  refine ⟨C2 * (Cm + Cl * (2+Cd)), by finiteness, ?_⟩
  intro u f hu0 hu2 hf heq
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 2 2 u H + iteratedWeakSobolevNorm 1 2 f H
  have huU := hu2.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right
  have hfU := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right
  have heqU := localized_principal_restrict_canonical hUH inter_subset_right hu2.memW1p heq
  obtain ⟨F, hF, hFn, hFeq⟩ := hdiff u f huU hfU heqU
  let p : E → ℝ := chosenWeakPartial' 2 l u (U ∩ H)
  have hp : MemWkp 1 2 p (U ∩ H) := huU.chosenWeakPartial_mem l
  obtain ⟨G, hG, hGn, hGeq⟩ := hloc p F hp hF hFeq
  let v : E → ℝ := fun x => χ x * p x
  have hv0 : MemW01p 2 v H := localized_tangential_derivative_zeroBoundary hU hu0 hu2 hχ hc hs l hl
  have hv1 : MemWkp 1 2 v H := memWkp_mul_smooth_of_tsupport_subset 1 isOpen_halfSpace hU hp hχ hc hs
  have hU : iteratedWeakSobolevNorm 2 2 u (U ∩ H) ≤ N :=
    (wkpNorm_mono_set (by norm_num) hUH inter_subset_right hu2).trans (le_add_right le_rfl)
  have hF1 : iteratedWeakSobolevNorm 1 2 f (U ∩ H) ≤ N :=
    (wkpNorm_mono_set (by norm_num) hUH inter_subset_right hf).trans (le_add_left le_rfl)
  have hpN : iteratedWeakSobolevNorm 1 2 p (U ∩ H) ≤ N :=
    (wkpNorm_chosenWeakPartial_le_wkpNorm_succ 1 2 u (U ∩ H) l).trans hU
  have hFN : iteratedWeakSobolevNorm 0 2 F (U ∩ H) ≤ (1+Cd)*N := by
    calc
      _ ≤ _ := hFn
      _ ≤ N + Cd*N := add_le_add hF1 (mul_le_mul le_rfl hU zero_le zero_le)
      _ = _ := by ring
  have hGN : eLpNorm G 2 (volume.restrict (U ∩ H)) ≤ Cl*(2+Cd)*N := by
    calc
      _ ≤ eLpNorm G 2 (volume.restrict H) := eLpNorm_mono_measure _ (Measure.restrict_mono_set volume inter_subset_right)
      _ = iteratedWeakSobolevNorm 0 2 G H := (wkpNorm_zero _ _ _).symm
      _ ≤ _ := hGn
      _ ≤ Cl*((1+Cd)*N+N) := by gcongr
      _ = _ := by ring
  have hvN : iteratedWeakSobolevNorm 1 2 v H ≤ Cm*N :=
    (hmul p hp).trans (mul_le_mul le_rfl hpN zero_le zero_le)
  have hGres : MemLp G 2 (volume.restrict (U ∩ H)) :=
    hG.memLp.mono_measure (Measure.restrict_mono_set volume inter_subset_right)
  have hGlocal : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U ∩ H →
      (∫ x in U ∩ H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j v H x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in U ∩ H, G x * φ x := by
    intro φ hφ hcφ hsφ
    simpa only [Finset.sum_mul] using Poincare.Analysis.Elliptic.weakEquation_congr_restrict
      (show U ∩ H ⊆ H from inter_subset_right) (a := B.a) (q := fun i => chosenWeakPartial' 2 i v H)
      (fun _ _ => rfl) (fun _ _ _ => rfl) hGeq φ hφ hcφ hsφ
  obtain ⟨hv2, hv2n⟩ := htwo v G hv0 hGres hGlocal
  have hae : v =ᵐ[volume.restrict (V ∩ H)] chosenWeakPartial' 2 l u (V ∩ H) := by
    filter_upwards [chosenWeakPartial'_mono_set_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hVH
      (inter_subset_inter_left H (subset_closure.trans hVU)) huU.memW1p l,
      ae_restrict_mem hVH.measurableSet] with x hx hxV
    change χ x * chosenWeakPartial' 2 l u (U ∩ H) x = _
    rw [hone x (subset_closure hxV.1), one_mul, hx]
  refine ⟨(MemWkp_congr_ae (by norm_num) hVH hae).mp hv2, ?_⟩
  rw [← wkpNorm_congr_ae (by norm_num) hVH hae]
  calc
    _ ≤ _ := hv2n
    _ ≤ C2*(Cm*N+Cl*(2+Cd)*N) := by gcongr
    _ = _ := by ring

#print axioms exists_flat_tangential_H3_estimate
end Yamabe3.Analysis.UniformElliptic
