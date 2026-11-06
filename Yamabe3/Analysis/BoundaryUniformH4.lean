import Yamabe3.Analysis.BoundaryUniformH4FromH3

/-! H4 boundary norm estimate with only the actual H2 solution and H2
source as inputs. H3 is produced on a larger compact neighborhood and
localized with its controlled commutator. -/
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
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_flat_H4_sobolev_estimate
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemW01p 2 u (halfSpace d) → MemWkp 2 2 u (halfSpace d) → MemWkp 2 2 f (halfSpace d) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ halfSpace d →
        (∫ x in halfSpace d, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in halfSpace d, f x * φ x) →
      MemWkp 4 2 u (V ∩ halfSpace d) ∧
      iteratedWeakSobolevNorm 4 2 u (V ∩ halfSpace d) ≤ K *
        (iteratedWeakSobolevNorm 2 2 u (halfSpace d) + iteratedWeakSobolevNorm 2 2 f (halfSpace d)) := by
  classical
  let H : Set E := halfSpace d
  obtain ⟨U, hU, hVU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  have hUH : IsOpen (U ∩ H) := hU.inter isOpen_halfSpace
  have hVH : IsOpen (V ∩ H) := hV.inter isOpen_halfSpace
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ := SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  obtain ⟨C3, hC3, hthree⟩ := exists_flat_H3_sobolev_estimate B hU hUc
  obtain ⟨Cl, hCl, hloc⟩ := exists_localized_source_uniform_bound 2 isOpen_halfSpace hU B.a B.smooth_a χ hχ hc hs
  obtain ⟨Cm, hCm, hmul⟩ := exists_localized_sobolev_multiplier_bound 3 isOpen_halfSpace hU χ hχ hc hs
  obtain ⟨C4, hC4, hfour⟩ := exists_flat_H4_of_H3_sobolev_estimate B hV hVc
  refine ⟨C4*(Cm*C3+Cl*(1+C3)), by finiteness, ?_⟩
  intro u f hu0 hu2 hf heq
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 2 2 u H + iteratedWeakSobolevNorm 2 2 f H
  obtain ⟨hu3, hu3n⟩ := hthree u f hu0 hu2 hf.le_succ heq
  have hu3N : iteratedWeakSobolevNorm 3 2 u (U ∩ H) ≤ C3*N := by
    apply hu3n.trans
    apply mul_le_mul le_rfl _ zero_le zero_le
    exact add_le_add le_rfl (wkpNorm_mono_order (by omega : 1 ≤ 2) f H)
  have hfU := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right
  have hfN : iteratedWeakSobolevNorm 2 2 f (U ∩ H) ≤ N :=
    (wkpNorm_mono_set (by norm_num) hUH inter_subset_right hf).trans (le_add_left le_rfl)
  have heqU := localized_principal_restrict_canonical hUH inter_subset_right hu2.memW1p heq
  obtain ⟨G, hG, hGn, hGeq⟩ := hloc u f hu3 hfU heqU
  let v : E → ℝ := fun x => χ x * u x
  have hv0 : MemW01p 2 v H := memW01p_mul_smooth isOpen_halfSpace hu0 hχ hc
  have hv3 : MemWkp 3 2 v H := memWkp_mul_smooth_of_tsupport_subset 3 isOpen_halfSpace hU hu3 hχ hc hs
  have hvN : iteratedWeakSobolevNorm 3 2 v H ≤ Cm*C3*N := by
    calc
      _ ≤ _ := hmul u hu3
      _ ≤ Cm*(C3*N) := mul_le_mul le_rfl hu3N zero_le zero_le
      _ = _ := by ring
  have hGN : iteratedWeakSobolevNorm 2 2 G H ≤ Cl*(1+C3)*N := by
    calc
      _ ≤ _ := hGn
      _ ≤ Cl*(N+C3*N) := by gcongr
      _ = _ := by ring
  obtain ⟨hv4, hv4n⟩ := hfour v G hv0 hv3 hG hGeq
  have hae : v =ᵐ[volume.restrict (V ∩ H)] u := by
    filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
    change χ x * u x = u x
    rw [hone x (subset_closure hx.1), one_mul]
  refine ⟨(MemWkp_congr_ae (by norm_num) hVH hae).mp hv4, ?_⟩
  rw [← wkpNorm_congr_ae (by norm_num) hVH hae]
  calc
    _ ≤ _ := hv4n
    _ ≤ C4*(Cm*C3*N+Cl*(1+C3)*N) := by gcongr
    _ = _ := by ring

#print axioms exists_flat_H4_sobolev_estimate
end Yamabe3.Analysis.UniformElliptic
