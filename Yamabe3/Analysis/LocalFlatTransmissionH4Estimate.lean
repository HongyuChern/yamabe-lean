import Yamabe3.Analysis.FlatSplitSource
import Yamabe3.Analysis.FlatTransmissionH4Estimate
import Yamabe3.Analysis.BoundedCompactSobolevExtension

/-! Quantitative flat transmission from the actual local source pieces.
Fixed compact extensions, not additional source data, supply the global
half-space inputs used by the tangential estimates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.NirenbergEuclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_local_flat_transmission_H4_estimate
    (B : SmoothEllipticBilinearForm 3 univ)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    (hW : IsOpen W) (hOW : closure O⊆W) :
    ∃ C : ℝ≥0∞,C≠⊤ ∧ ∀ u f g : E → ℝ,
      MemWkp 2 2 u O → MemWkp 2 2 f W → MemWkp 2 2 g W →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,flatSplitSource f g x*φ x) →
      MemWkp 4 2 u (V∩halfSpace 3) ∧
      iteratedWeakSobolevNorm 4 2 u (V∩halfSpace 3) ≤ C *
        (iteratedWeakSobolevNorm 2 2 u O+
          (iteratedWeakSobolevNorm 2 2 f W+iteratedWeakSobolevNorm 2 2 g W)) := by
  obtain ⟨A,hA,ha⟩ := exists_flat_transmission_positive_H4_estimate B hO hOc hV hVc hVO
  obtain ⟨T,hT,ht⟩ := exists_bounded_compact_sobolev_extension 2 hOc hW hOW
  refine ⟨A*(1+T),by finiteness,?_⟩
  intro u f g hu hf hg heq
  obtain ⟨F,hFc,hF,hFf,hFn⟩ := ht f hf
  obtain ⟨G,hGc,hG,hGg,hGn⟩ := ht g hg
  let N := normalScaling (d:=3) (-1) (by norm_num)
  have hGN : MemWkp 2 2 (G∘N) univ := by
    simpa only [preimage_univ,N,Function.comp_def] using memWkp_comp_normalScaling
      (by norm_num : (-1:ℝ)≠0) isOpen_univ (by norm_num) 2 hG
  have hFH := hF.mono_set (by norm_num : (1:ℝ≥0∞)≤2) isOpen_halfSpace (subset_univ _)
  have hGH := hGN.mono_set (by norm_num : (1:ℝ≥0∞)≤2) isOpen_halfSpace (subset_univ _)
  have hsrc : twoSidedHalfSource F (G∘N) =ᵐ[volume.restrict O] flatSplitSource f g := by
    change twoSidedHalfSource F (fun x => G (normalScaling (-1) (by norm_num) x)) =ᵐ[volume.restrict O] _
    rw [twoSidedHalfSource_reflection_eq]
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact flatSplitSource_congr_on (hFf.mono subset_closure) (hGg.mono subset_closure) hx
  have hh := ha u F (G∘N) hu hFH hGH (by
    intro φ hφ hc hs
    rw [heq φ hφ hc hs]
    exact integral_congr_ae (hsrc.symm.mono (fun x hx => congrArg (·*φ x) hx)))
  have hFnH := (wkpNorm_mono_set (by norm_num : (1:ℝ≥0∞)≤2) isOpen_halfSpace (subset_univ _) hF).trans hFn
  have hGnH : iteratedWeakSobolevNorm 2 2 (G∘N) (halfSpace 3)≤T*iteratedWeakSobolevNorm 2 2 g W := by
    have hh := wkpNorm_mono_set (by norm_num : (1:ℝ≥0∞)≤2) isOpen_halfSpace (subset_univ _) hGN
    have he := sobolevNorm_comp_normalReflection isOpen_univ 2 hG
    simp only [preimage_univ] at he
    exact hh.trans (he.le.trans hGn)
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ A*(iteratedWeakSobolevNorm 2 2 u O+
        T*(iteratedWeakSobolevNorm 2 2 f W+iteratedWeakSobolevNorm 2 2 g W)) := by
      rw [mul_add T]
      exact mul_le_mul le_rfl (add_le_add le_rfl (add_le_add hFnH hGnH)) zero_le zero_le
    _ ≤ A*((1+T)*(iteratedWeakSobolevNorm 2 2 u O+
        (iteratedWeakSobolevNorm 2 2 f W+iteratedWeakSobolevNorm 2 2 g W))) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      rw [mul_add (1+T)]
      apply add_le_add
      · exact (one_mul _).symm.le.trans (mul_le_mul (le_add_right le_rfl) le_rfl zero_le zero_le)
      · exact mul_le_mul (le_add_left le_rfl) le_rfl zero_le zero_le
    _ = _ := (mul_assoc _ _ _).symm

#print axioms exists_local_flat_transmission_H4_estimate
end Yamabe3.Analysis.UniformElliptic
