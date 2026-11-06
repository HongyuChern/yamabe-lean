import Yamabe3.Analysis.BoundaryLocalH3Estimate

/-! Local quantitative H4 from the original H1 zero-boundary solution
and the actual local H2 source. Intermediate regularity is produced.
Constants are fixed before source/solution for a fixed elliptic form. -/
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

theorem exists_flat_local_H4_sobolev_estimate
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u f : E → ℝ),
      MemW01p 2 u (halfSpace d) → MemWkp 2 2 f (W ∩ halfSpace d) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ halfSpace d →
        (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W ∩ halfSpace d, f x * φ x) →
      MemWkp 4 2 u (V ∩ halfSpace d) ∧
      iteratedWeakSobolevNorm 4 2 u (V ∩ halfSpace d) ≤ K *
        (iteratedWeakSobolevNorm 1 2 u (halfSpace d) + iteratedWeakSobolevNorm 2 2 f (W ∩ halfSpace d)) := by
  classical
  let H : Set E := halfSpace d
  obtain ⟨U, hU, hVU, hUW⟩ := hVc.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hVW)
  have hUc : IsCompact (closure U) := hWc.of_isClosed_subset isClosed_closure (hUW.trans subset_closure)
  have hUH : IsOpen (U ∩ H) := hU.inter isOpen_halfSpace
  have hVH : IsOpen (V ∩ H) := hV.inter isOpen_halfSpace
  have hUW' : U ∩ H ⊆ W ∩ H := inter_subset_inter_left _ (subset_closure.trans hUW)
  obtain ⟨χ, hχ, hc, -, hone, hs⟩ := SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
  obtain ⟨Cp, hCp, hprev⟩ := exists_flat_local_H3_sobolev_estimate B hW hWc hU hUc hUW
  obtain ⟨Cl, hCl, hloc⟩ := exists_localized_source_uniform_bound 2 isOpen_halfSpace hU B.a B.smooth_a χ hχ hc hs
  obtain ⟨Cm, hCm, hmul⟩ := exists_localized_sobolev_multiplier_bound 3 isOpen_halfSpace hU χ hχ hc hs
  obtain ⟨Cn, hCn, hnext⟩ := exists_flat_H4_of_H3_sobolev_estimate B hV hVc
  refine ⟨Cn*(Cm*Cp+Cl*(1+Cp)), by finiteness, ?_⟩
  intro u f hu0 hf heq
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 1 2 u H + iteratedWeakSobolevNorm 2 2 f (W ∩ H)
  obtain ⟨huP, huPn⟩ := hprev u f hu0 hf.le_succ heq
  have huPN : iteratedWeakSobolevNorm 3 2 u (U ∩ H) ≤ Cp*N := by
    apply huPn.trans
    apply mul_le_mul le_rfl _ zero_le zero_le
    apply add_le_add le_rfl
    exact wkpNorm_mono_order (by omega : 1 ≤ 2) f (W ∩ H)
  have hfU := hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH hUW'
  have hfN : iteratedWeakSobolevNorm 2 2 f (U ∩ H) ≤ N :=
    (wkpNorm_mono_set (by norm_num) hUH hUW' hf).trans (le_add_left le_rfl)
  have heqU : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U ∩ H →
      (∫ x in U ∩ H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (U ∩ H) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in U ∩ H, f x * φ x := by
    intro φ hφ hcφ hsφ
    have hh := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hUW'
      (a := B.a) (q := fun i => chosenWeakPartial' 2 i u H)
      (fun _ _ => rfl) (fun _ _ _ => rfl) heq φ hφ hcφ hsφ
    simp only [Finset.sum_mul] at hh
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [eventually_all.mpr (fun j => chosenWeakPartial'_mono_set_ae
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hUH inter_subset_right hu0.1 j)] with x hx
    simp only [← hx]
  obtain ⟨G, hG, hGn, hGeq⟩ := hloc u f huP hfU heqU
  let v : E → ℝ := fun x => χ x * u x
  have hv0 : MemW01p 2 v H := memW01p_mul_smooth isOpen_halfSpace hu0 hχ hc
  have hvP : MemWkp 3 2 v H := memWkp_mul_smooth_of_tsupport_subset 3 isOpen_halfSpace hU huP hχ hc hs
  have hvN : iteratedWeakSobolevNorm 3 2 v H ≤ Cm*Cp*N := by
    calc
      _ ≤ _ := hmul u huP
      _ ≤ Cm*(Cp*N) := mul_le_mul le_rfl huPN zero_le zero_le
      _ = _ := by ring
  have hGN : iteratedWeakSobolevNorm 2 2 G H ≤ Cl*(1+Cp)*N := by
    calc
      _ ≤ _ := hGn
      _ ≤ Cl*(N+Cp*N) := by gcongr
      _ = _ := by ring
  obtain ⟨hvNext, hvNextN⟩ := hnext v G hv0 hvP hG hGeq
  have hae : v =ᵐ[volume.restrict (V ∩ H)] u := by
    filter_upwards [ae_restrict_mem hVH.measurableSet] with x hx
    change χ x * u x = u x
    rw [hone x (subset_closure hx.1), one_mul]
  refine ⟨(MemWkp_congr_ae (by norm_num) hVH hae).mp hvNext, ?_⟩
  rw [← wkpNorm_congr_ae (by norm_num) hVH hae]
  calc
    _ ≤ _ := hvNextN
    _ ≤ Cn*(Cm*Cp*N+Cl*(1+Cp)*N) := by gcongr
    _ = _ := by ring

#print axioms exists_flat_local_H4_sobolev_estimate
end Yamabe3.Analysis.UniformElliptic
