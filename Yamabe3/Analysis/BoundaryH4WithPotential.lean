import Yamabe3.Analysis.BoundaryLocalH4Estimate

/-! Boundary H4 for the original H1-zero solution with a smooth potential.
The potential term is bootstrapped on the same function; it is not required
to be H2 as an extra premise. The constants here are for fixed B and b. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_flat_H4_with_potential_bound
    (B : SmoothEllipticBilinearForm d univ) (b : E → ℝ) (hb : ContDiff ℝ ∞ b)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (u F : E → ℝ),
      MemW01p 2 u (halfSpace d) → MemWkp 2 2 F (W ∩ halfSpace d) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ halfSpace d →
        (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W ∩ halfSpace d, (F x + b x * u x) * φ x) →
      MemWkp 4 2 u (V ∩ halfSpace d) ∧
      iteratedWeakSobolevNorm 4 2 u (V ∩ halfSpace d) ≤ K *
        (iteratedWeakSobolevNorm 1 2 u (halfSpace d) + iteratedWeakSobolevNorm 2 2 F (W ∩ halfSpace d)) := by
  classical
  let H : Set E := halfSpace d
  have hWH : IsOpen (W ∩ H) := hW.inter isOpen_halfSpace
  have hWHc : IsCompact (closure (W ∩ H)) := hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨U, hU, hVU, hUW⟩ := hVc.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hVW)
  have hUc : IsCompact (closure U) := hWc.of_isClosed_subset isClosed_closure (hUW.trans subset_closure)
  have hUH : IsOpen (U ∩ H) := hU.inter isOpen_halfSpace
  have hUHc : IsCompact (closure (U ∩ H)) := hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hUW' : U ∩ H ⊆ W ∩ H := inter_subset_inter_left _ (subset_closure.trans hUW)
  obtain ⟨C0, hC0, hb0⟩ := exists_compact_sobolev_multiplier_bound 0 hWH hWHc b hb
  obtain ⟨C2, hC2, hb2⟩ := exists_compact_sobolev_multiplier_bound 2 hUH hUHc b hb
  obtain ⟨K2, hK2, hh2⟩ := exists_flat_H2_sobolev_estimate B hW hWc hU hUc hUW
  obtain ⟨K4, hK4, hh4⟩ := exists_flat_local_H4_sobolev_estimate B hU hUc hV hVc hVU
  refine ⟨K4*(2+C2*K2*(2+C0)), by finiteness, ?_⟩
  intro u F hu0 hF heq
  let N := iteratedWeakSobolevNorm 1 2 u H + iteratedWeakSobolevNorm 2 2 F (W ∩ H)
  let G : E → ℝ := fun x => F x + b x * u x
  have hu1 : MemWkp 1 2 u H := (MemWkp.one_iff_memW1p).mpr hu0.1
  have huW := hu1.mono_set (by norm_num) hWH inter_subset_right
  have hbmem : MemLp (fun x => b x * u x) 2 (volume.restrict (W ∩ H)) :=
    memWkp_mul_smooth_of_isCompact_closure 0 hWH hWHc huW.memLp hb
  have hG0 : MemLp G 2 (volume.restrict (W ∩ H)) := hF.memLp.add hbmem
  have huN : eLpNorm u 2 (volume.restrict (W ∩ H)) ≤ N := by
    apply le_trans (eLpNorm_mono_measure u (Measure.restrict_mono_set volume inter_subset_right))
    apply le_trans _ (le_add_right le_rfl)
    simpa only [wkpNorm_zero] using wkpNorm_mono_order (p := (2 : ℝ≥0∞)) (by norm_num : 0 ≤ 1) u H
  have hFN : eLpNorm F 2 (volume.restrict (W ∩ H)) ≤ N := by
    apply le_trans _ (le_add_left le_rfl)
    simpa only [wkpNorm_zero] using wkpNorm_mono_order (p := (2 : ℝ≥0∞)) (by norm_num : 0 ≤ 2) F (W ∩ H)
  have hG0N : eLpNorm G 2 (volume.restrict (W ∩ H)) ≤ (1+C0)*N := by
    calc
      _ ≤ eLpNorm F 2 (volume.restrict (W ∩ H)) + eLpNorm (fun x => b x * u x) 2 (volume.restrict (W ∩ H)) :=
        eLpNorm_add_le hF.memLp.1 hbmem.1 (by norm_num)
      _ ≤ N + C0*eLpNorm u 2 (volume.restrict (W ∩ H)) :=
        add_le_add hFN (by simpa only [wkpNorm_zero] using hb0 u huW.memLp)
      _ ≤ N+C0*N := add_le_add le_rfl (mul_le_mul le_rfl huN zero_le zero_le)
      _ = _ := by ring
  obtain ⟨hu2, hu2n⟩ := hh2 u G hu0 hG0 heq
  have hu2N : iteratedWeakSobolevNorm 2 2 u (U ∩ H) ≤ K2*(2+C0)*N := by
    calc
      _ ≤ _ := hu2n
      _ ≤ K2*(N+(1+C0)*N) := mul_le_mul le_rfl
        (add_le_add (le_add_right le_rfl) hG0N) zero_le zero_le
      _ = _ := by ring
  have hFU := hF.mono_set (by norm_num) hUH hUW'
  have hbU := memWkp_mul_smooth_of_isCompact_closure 2 hUH hUHc hu2 hb
  have hG2 : MemWkp 2 2 G (U ∩ H) := MemWkp.add (by norm_num) hUH hFU hbU
  have hG2N : iteratedWeakSobolevNorm 2 2 G (U ∩ H) ≤ (1+C2*K2*(2+C0))*N := by
    calc
      _ ≤ iteratedWeakSobolevNorm 2 2 F (U ∩ H) + iteratedWeakSobolevNorm 2 2 (fun x => b x * u x) (U ∩ H) :=
        wkpNorm_add_le (by norm_num) hUH hFU hbU
      _ ≤ N + C2 * iteratedWeakSobolevNorm 2 2 u (U ∩ H) :=
        add_le_add ((wkpNorm_mono_set (by norm_num) hUH hUW' hF).trans (le_add_left le_rfl)) (hb2 u hu2)
      _ ≤ N + C2*(K2*(2+C0)*N) := add_le_add le_rfl (mul_le_mul le_rfl hu2N zero_le zero_le)
      _ = _ := by ring
  have heqU : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U ∩ H →
      (∫ x in U ∩ H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u H x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in U ∩ H, G x * φ x := by
    intro φ hφ hc hs
    have h := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hUW'
      (a := B.a) (q := fun j => chosenWeakPartial' 2 j u H)
      (fun _ _ => rfl) (fun _ _ _ => rfl) heq φ hφ hc hs
    simpa only [Finset.sum_mul] using h
  obtain ⟨hu4, hu4n⟩ := hh4 u G hu0 hG2 heqU
  refine ⟨hu4, ?_⟩
  calc
    _ ≤ _ := hu4n
    _ ≤ K4*(N+(1+C2*K2*(2+C0))*N) := mul_le_mul le_rfl
      (add_le_add (le_add_right le_rfl) hG2N) zero_le zero_le
    _ = _ := by ring

#print axioms exists_flat_H4_with_potential_bound
end Yamabe3.Analysis.UniformElliptic
